import socket
import threading
import struct
import hashlib
import os
import time
import json
import argparse
from typing import Dict, Tuple, List, Optional, Any, Set

from card_engine import (
    CardDatabaseEngine,
    compute_all_scores,
    parse_card_cost,
    verify_chaining,
    sha256_hex,
    sha256_hash,
    RESOURCE_KEYS
)

MSG_LOBBY_PRESENCE   = 0x01
MSG_LOBBY_LEAVE      = 0x02
MSG_LOBBY_START_VOTE = 0x03
MSG_LOBBY_START_ACK  = 0x04
MSG_HELLO            = 0x05
MSG_HELLO_ACK        = 0x06
MSG_SEED_COMMIT      = 0x07
MSG_SEED_REVEAL      = 0x08
MSG_RING_CONFIRM     = 0x09
MSG_CARD_COMMIT      = 0x0A
MSG_CARD_REVEAL      = 0x0B
MSG_ACTION_ANNOUNCE  = 0x0C
MSG_HAND_PASS        = 0x0D
MSG_RESOURCE_QUERY   = 0x0E
MSG_RESOURCE_OFFER   = 0x0F
MSG_RESOURCE_BUY     = 0x10
MSG_AGE_END          = 0x11
MSG_SCORE_REPORT     = 0x12
MSG_GAME_END         = 0x13
MSG_ERROR            = 0x14
MSG_PING             = 0x15
MSG_PONG             = 0x16
MSG_DISCONNECT       = 0x17
MSG_DIRECT_MESSAGE   = 0x18
MSG_GROUP_MESSAGE    = 0x19
MSG_SPECTATOR_SYNC   = 0x20

OPCODE_NAMES = {
    0x01: "LOBBY_PRESENCE", 0x02: "LOBBY_LEAVE", 0x03: "LOBBY_START_VOTE",
    0x04: "LOBBY_START_ACK", 0x05: "HELLO", 0x06: "HELLO_ACK",
    0x07: "SEED_COMMIT", 0x08: "SEED_REVEAL", 0x09: "RING_CONFIRM",
    0x0A: "CARD_COMMIT", 0x0B: "CARD_REVEAL", 0x0C: "ACTION_ANNOUNCE",
    0x0D: "HAND_PASS", 0x0E: "RESOURCE_QUERY", 0x0F: "RESOURCE_OFFER",
    0x10: "RESOURCE_BUY", 0x11: "AGE_END", 0x12: "SCORE_REPORT",
    0x13: "GAME_END", 0x14: "ERROR", 0x15: "PING", 0x16: "PONG",
    0x17: "DISCONNECT", 0x18: "DIRECT_MESSAGE", 0x19: "GROUP_MESSAGE",
    0x20: "SPECTATOR_SYNC"
}

UNRELIABLE_MESSAGES = {
    MSG_LOBBY_PRESENCE, MSG_LOBBY_LEAVE, MSG_LOBBY_START_VOTE,
    MSG_LOBBY_START_ACK, MSG_PING, MSG_PONG, MSG_DISCONNECT, MSG_SPECTATOR_SYNC
}

FLAG_ACK = 0x01
FLAG_RETRANSMIT = 0x02

HEADER_FORMAT = "!BBBB 16s H H I I"
HEADER_SIZE = struct.calcsize(HEADER_FORMAT)
assert HEADER_SIZE == 32

RTO_INIT = 0.200
RTO_MAX = 3.200
RETRY_MAX = 6
T_LOBBY_ANNOUNCE_INTERVAL = 2.0
T_LOBBY_STALE = 6.0
T_LOBBY_QUIET = 3.0
T_LOBBY_TIMEOUT = 120.0
MIN_PLAYERS = 3
MAX_PLAYERS = 7
T_SEED_TIMEOUT = 10.0       # RFC 10: SEED_COMMIT / SEED_REVEAL barrier window
T_TURN_TIMEOUT = 8.0        # RFC 10: CARD_COMMIT barrier window
T_RESOURCE_TIMEOUT = 5.0    # RFC 10: RESOURCE_OFFER reply window (also PING corroboration window)
T_SCORE_TIMEOUT = 10.0      # RFC 10: SCORE_REPORT barrier window
T_JOIN_TIMEOUT = 10.0       # RFC 10: HELLO collection window (7.5 / 11.1)

def clip_text(text: str, limit: int = 1000) -> str:
    """RFC 8.3: chat text must be <= 1000 bytes of UTF-8."""
    return text.encode("utf-8")[:limit].decode("utf-8", "ignore")


def _turn_locked(fn):
    """Run a turn-state method while holding the node's turn lock (listener thread and resolve thread share state)."""
    def wrapper(self, *args, **kwargs):
        with self._turn_lock:
            return fn(self, *args, **kwargs)
    wrapper.__name__ = fn.__name__
    return wrapper


class Peer7WDNode:
    def __init__(self, display_name: str, room_code: str, host: str, game_port: int,
                 lobby_port: int = 7777, verbose: bool = False, spectator: bool = False,
                 card_db: str = "Card Database 7WD.xlsx", drop_to: Optional[List[int]] = None):
        self.display_name = display_name
        self.room_code = room_code
        self.host = host
        self.game_port = game_port
        self.lobby_port = lobby_port
        self.verbose = verbose
        self.logged_broadcasts: Set[Tuple] = set()
        self.spectator = spectator
        self.running = True

        self.session_id = sha256_hash(room_code.encode("utf-8"))[:16]
        self.lobby_peer_id = os.urandom(16).hex()
        self.manifest_peer_id = 0xFFFF

        self.lobby_roster: Dict[str, dict] = {}
        self.last_roster_change = time.time()
        self.seeking_start_time = time.time()
        self.lobby_closed = False
        self.collected_start_acks: Set[str] = set()

        self.manifest: Dict[int, Tuple[str, int]] = {}
        self.manifest_names: Dict[int, str] = {}
        self.hello_acks_received: Set[int] = set()
        self.spectator_addrs: Set[Tuple[str, int]] = set()

        self.channel_seq: Dict[int, int] = {}
        self.channel_highest_ack: Dict[int, int] = {}
        self.unacked_packets: Dict[Tuple[int, int], dict] = {}
        self.channel_rto: Dict[int, float] = {}
        self.channel_rtt: Dict[int, float] = {}
        self.channel_rto_base: Dict[int, float] = {}
        self.delivered_seqs: Dict[int, Set[int]] = {}

        self.my_nonce = os.urandom(32)
        self.my_commitment = sha256_hex(self.my_nonce)
        self.collected_commits: Dict[int, str] = {}
        self.collected_reveals: Dict[int, bytes] = {}
        self.shared_seed: Optional[bytes] = None
        self.seating_order: List[int] = []
        self.my_seat = 0
        self.my_wonder_board: Dict[str, Any] = {}
        self.all_wonders: Dict[int, Dict[str, Any]] = {}
        self.selected_guilds: List[str] = []

        self.card_engine = CardDatabaseEngine(card_db)
        self.current_age = 1
        self.current_turn = 1
        self.current_hand: List[Dict[str, Any]] = []

        self.coins = 3
        self.resources = {r: 0 for r in RESOURCE_KEYS}
        self.trade_discounts = {"raw_left": 2, "raw_right": 2, "mfg": 2}
        self.built_cards: List[Dict[str, Any]] = []
        self.military_shields = 0
        self.military_tokens: List[int] = []
        self.science_symbols: List[str] = []
        self.wonder_stages_built = 0

        self.public_tableaus: Dict[int, Dict[str, Any]] = {}

        self.card_commits: Dict[int, str] = {}
        self.card_reveals: Dict[int, dict] = {}
        self.action_announcements: Dict[int, dict] = {}
        self.age_end_shields: Dict[int, int] = {}
        self.collected_score_reports: Dict[int, dict] = {}
        self.game_end_broadcasted = False

        self.resources_bought_this_turn: List[Dict[str, Any]] = []
        self.pending_offers: Dict[int, Dict[str, int]] = {}
        self.offer_event = threading.Event()
        self.pending_seed_reveals: Dict[int, bytes] = {}
        self.my_pass_sent = False                      # my outbound HAND_PASS for this turn has been sent
        self.inbound_hands: List[dict] = []            # neighbour HAND_PASSes, held until my own turn is finished
        self.pending_card_reveals: Dict[int, dict] = {}

        self.chosen_card: Optional[Dict[str, Any]] = None
        self.chosen_action: str = "BUILD"
        self.chosen_nonce: bytes = b""
        self.revealed_this_turn = False
        self.announced_this_turn = False

        self.incident_reports: Dict[str, Set[int]] = {}
        self.disconnected_peers: Set[int] = set()
        # --- DISCONNECT / liveness state (RFC 6.3, 7.9, 11.3) ---
        self.aborted = False
        self.failed_channels: Set[int] = set()      # 6.3: our sending direction to these peers is permanently failed
        self.incidents: Dict[str, dict] = {}        # 7.9: incident_id -> {offender, reporters, echoed, ...}
        self.last_pong: Dict[int, float] = {}
        self.turn_misses: Dict[int, int] = {}       # consecutive missed CARD_COMMIT barriers per peer
        self.turn_absent: Set[int] = set()          # peers excluded from THIS turn's barriers only
        self.turn_phase_start: Optional[float] = None
        self.seed_phase_start: Optional[float] = None
        self.score_phase_start: Optional[float] = None
        self.drop_to_pids: Set[int] = set(drop_to or [])   # TEST ONLY: swallow outgoing packets to these peers
        self.last_heard: Dict[int, float] = {}               # 7.5: last datagram of any kind from each manifest peer
        self.join_deadline: Optional[float] = None
        self.lost_passes: Dict[int, List[dict]] = {}          # HAND_PASSes that never got through to a failed channel
        self.last_pass: Optional[Tuple[int, dict]] = None    # (target_pid, payload) of my latest HAND_PASS
        self.state_lock = threading.Lock()
        self._turn_lock = threading.RLock()

        # UDP Sockets Setup
        self.game_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.game_sock.bind((self.host, self.game_port))

        self.lobby_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.lobby_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            self.lobby_sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            self.lobby_sock.bind(("", self.lobby_port))
        except Exception:
            self.lobby_sock.bind((self.host, self.lobby_port))

        threading.Thread(target=self._lobby_listener, daemon=True).start()
        threading.Thread(target=self._game_listener, daemon=True).start()
        threading.Thread(target=self._retransmission_daemon, daemon=True).start()
        threading.Thread(target=self._barrier_watchdog, daemon=True).start()
        threading.Thread(target=self._lobby_gossip_daemon, daemon=True).start()

    def log(self, direction: str, addr: Tuple[str, int], opcode: int, seq: int, ack: int, flags: int, payload: dict):
        if not self.verbose:
            return
        key = (direction, opcode, json.dumps(payload, sort_keys=True))
        if key in self.logged_broadcasts:
            return
        self.logged_broadcasts.add(key)
        name = OPCODE_NAMES.get(opcode, f"0x{opcode:02X}")
        ts = time.strftime("%H:%M:%S")
        flag_str = ""
        if flags & FLAG_ACK: flag_str += "[ACK]"
        if flags & FLAG_RETRANSMIT: flag_str += "[RETX]"
        print(f"[{ts}] [{direction}] {addr[0]}:{addr[1]} | {name} (0x{opcode:02X}) | Seq={seq} Ack={ack} {flag_str}")
        print(f"       Payload: {json.dumps(payload)}")

    def pack_packet(self, opcode: int, payload: dict, seq: int = 0, ack: int = 0, flags: int = 0) -> bytes:
        body = json.dumps(payload).encode("utf-8")
        header = struct.pack(
            HEADER_FORMAT, 1, opcode, flags, 0, self.session_id,
            self.manifest_peer_id, len(body), seq, ack
        )
        return header + body

    def unpack_packet(self, data: bytes) -> Tuple[int, int, int, bytes, int, int, int, dict]:
        if len(data) < HEADER_SIZE:
            raise ValueError("Datagram smaller than 32-byte header")
        ver, opcode, flags, reserved, sess_id, sender_pid, plen, seq, ack = struct.unpack(
            HEADER_FORMAT, data[:HEADER_SIZE]
        )
        if ver != 1:
            raise ValueError(f"Unsupported protocol version {ver}")
        body_bytes = data[HEADER_SIZE:HEADER_SIZE + plen]
        payload = json.loads(body_bytes.decode("utf-8")) if plen > 0 else {}
        return opcode, flags, sender_pid, sess_id, plen, seq, ack, payload

    def send_reliable(self, target_pid: int, opcode: int, payload: dict):
        # RFC 6.3: once a channel has failed (or the peer is DISCONNECTED) we MUST NOT resume delivery on it.
        if target_pid not in self.manifest or self.spectator:
            return
        if target_pid in self.failed_channels:
            if opcode == MSG_HAND_PASS and target_pid not in self.disconnected_peers:
                self.lost_passes.setdefault(target_pid, []).append(payload)   # keep it: may need re-routing on DISCONNECT
            return
        addr = self.manifest[target_pid]

        with self.state_lock:
            cur_seq = self.channel_seq.get(target_pid, 1)
            self.channel_seq[target_pid] = cur_seq + 1
            ack_to_piggyback = self.channel_highest_ack.get(target_pid, 0)
            flags = FLAG_ACK if ack_to_piggyback > 0 else 0

            raw = self.pack_packet(opcode, payload, seq=cur_seq, ack=ack_to_piggyback, flags=flags)
            self.unacked_packets[(target_pid, cur_seq)] = {
                "raw": raw, "addr": addr, "target_pid": target_pid, "opcode": opcode,
                "retries": 0, "last_sent": time.time(), "payload": payload, "seq": cur_seq
            }

        self._raw_send(raw, addr)
        self.log("SENT", addr, opcode, cur_seq, ack_to_piggyback, flags, payload)

    def send_unreliable(self, addr: Tuple[str, int], opcode: int, payload: dict, ack_target: int = 0):
        flags = FLAG_ACK if ack_target > 0 else 0
        raw = self.pack_packet(opcode, payload, seq=0, ack=ack_target, flags=flags)
        try:
            self._raw_send(raw, addr)
        except Exception:
            pass
        self.log("SENT", addr, opcode, 0, ack_target, flags, payload)

    def send_bare_ack(self, target_pid: int, ack_number: int):
        if target_pid in self.manifest:
            addr = self.manifest[target_pid]
            raw = self.pack_packet(0, {}, seq=0, ack=ack_number, flags=FLAG_ACK)
            try:
                self._raw_send(raw, addr)
            except Exception:
                pass
            self.log("SENT", addr, 0, 0, ack_number, FLAG_ACK, {})

    def broadcast_mesh(self, opcode: int, payload: dict, reliable: bool = True):
        if self.spectator:
            return
        for pid in list(self.manifest.keys()):
            if pid != self.manifest_peer_id and pid not in self.disconnected_peers:
                if reliable and (opcode not in UNRELIABLE_MESSAGES):
                    self.send_reliable(pid, opcode, payload)
                else:
                    self.send_unreliable(self.manifest[pid], opcode, payload)

        for s_addr in list(self.spectator_addrs):
            self.send_unreliable(s_addr, opcode, payload)

    def broadcast_error(self, code: str, detail: str, offending_pid: Optional[int] = None,
                        incident_id: Optional[str] = None):
        payload = {"code": code, "detail": detail}
        if incident_id is not None:
            payload["incident_id"] = incident_id      # RFC 8.3: REQUIRED for TIMEOUT incidents (7.9)
        if offending_pid is not None:
            # RFC 8.3: offending_peer is a SEAT (falls back to the peer id before the ring exists)
            payload["offending_peer"] = self.seating_order.index(offending_pid) if offending_pid in self.seating_order else offending_pid
        print(f"\n[!] RAISING ERROR {code}: {detail}")
        self.broadcast_mesh(MSG_ERROR, payload)

    def leave_lobby(self):
        if self.lobby_closed:
            return
        payload = {"lobby_peer_id": self.lobby_peer_id}
        raw = self.pack_packet(MSG_LOBBY_LEAVE, payload, seq=0, ack=0)
        self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_LEAVE, 0, 0, 0, payload)
        targets = [("<broadcast>", self.lobby_port), ("127.0.0.1", self.lobby_port)]
        for info in list(self.lobby_roster.values()):
            targets.append((info["host"], info["port"]))
        for dest in targets:
            try:
                self.lobby_sock.sendto(raw, dest)
            except Exception:
                pass

    # ==================================================================
    # DISCONNECT (0x17) - RFC 6.3, 7.6, 7.9, 7.11, 11.1, 11.3
    #
    #  * Broadcast-observable misses (SEED_COMMIT/REVEAL, SCORE_REPORT, bad SEED_REVEAL) are
    #    decided by every peer independently, single miss.
    #  * CARD_COMMIT barrier: two consecutive T_TURN_TIMEOUT misses.
    #  * Directed/private failures (RESOURCE_QUERY timeout, RETRY_MAX on a channel) are NEVER
    #    unilateral: they open an incident (ERROR TIMEOUT + incident_id) and the peer is only
    #    marked DISCONNECTED once EVERY other live peer has echoed the same incident_id.
    #  * "Marked DISCONNECTED" is a local state on each peer; the DISCONNECT message itself
    #    ({reason}) is a peer announcing ITS OWN exit (USER_QUIT / QUORUM_LOST).
    # ==================================================================
    def _raw_send(self, raw: bytes, addr: Tuple[str, int]):
        """Single choke point for game-channel datagrams (lets --drop-to / 'drop' simulate a dead link)."""
        if self.drop_to_pids:
            for pid, a in self.manifest.items():
                if a == addr and pid in self.drop_to_pids:
                    return
        self.game_sock.sendto(raw, addr)

    def _pname(self, pid: int) -> str:
        return self.manifest_names.get(pid, f"Player {pid}")

    def _live_pids(self) -> List[int]:
        return sorted(p for p in self.manifest if p not in self.disconnected_peers)

    def _live_ring(self) -> List[int]:
        """The ring is NOT recomputed (11.3): disconnected seats are simply skipped."""
        return [p for p in self.seating_order if p not in self.disconnected_peers]

    def _neighbor_pid(self, offset: int) -> int:
        ring = self._live_ring()
        if self.manifest_peer_id not in ring or len(ring) < 2:
            return self.manifest_peer_id
        return ring[(ring.index(self.manifest_peer_id) + offset) % len(ring)]

    def _expected_peers(self) -> Set[int]:
        return set(self._live_ring()) - self.turn_absent

    def announce_exit(self, reason: str):
        """Best-effort DISCONNECT {reason} for OUR OWN exit; repeated because it is unreliable (8.1)."""
        if self.spectator or not self.lobby_closed or self.manifest_peer_id == 0xFFFF:
            return
        for _ in range(3):
            self.broadcast_mesh(MSG_DISCONNECT, {"reason": reason}, reliable=False)
            time.sleep(0.05)

    def _abort_quorum_lost(self):
        if self.aborted:
            return
        self.aborted = True
        print(f"\n[!] QUORUM LOST: fewer than {MIN_PLAYERS} live peers remain. Session ABORTED (RFC 11.1/11.3). Press Enter to exit.")
        self.announce_exit("QUORUM_LOST")
        self.running = False

    def _mark_disconnected(self, pid: int, reason: str):
        with self._turn_lock:
            if pid == self.manifest_peer_id or pid in self.disconnected_peers or pid not in self.manifest:
                return
            self.disconnected_peers.add(pid)
            lost_passes = list(self.lost_passes.pop(pid, []))
            with self.state_lock:
                self.failed_channels.add(pid)
                for key in sorted(k for k in self.unacked_packets if k[0] == pid):
                    item = self.unacked_packets[key]
                    if item["opcode"] == MSG_HAND_PASS:
                        lost_passes.append(item["payload"])      # never ACKed -> the dead seat never got it
                    del self.unacked_packets[key]
            self.pending_offers.pop(pid, None)
            self.pending_seed_reveals.pop(pid, None)
            self.pending_card_reveals.pop(pid, None)
            print(f"\n[!] PEER DISCONNECTED: {self._pname(pid)} (peer {pid}) | reason: {reason}")
            if len(self._live_pids()) < MIN_PLAYERS:
                self._abort_quorum_lost()
                return
            # 11.3: the Ring is not recomputed. Every HAND_PASS that was still un-ACKed when the seat died is lost,
            # even if I have already advanced to my next turn, so re-send each one to the next live seat.
            for pl in lost_passes:
                if pl.get("turn") == 6:
                    continue
                direction = -1 if pl.get("age", self.current_age) in (1, 3) else 1
                new_target = self._neighbor_pid(direction)
                if new_target != self.manifest_peer_id:
                    print(f"[*] Re-routing my HAND_PASS (Age {pl.get('age')}, Turn {pl.get('turn')}) around the disconnected seat to {self._pname(new_target)} (peer {new_target})")
                    self.send_reliable(new_target, MSG_HAND_PASS, pl)
                    self.last_pass = (new_target, pl)
            self._recheck_everything()

    def _recheck_everything(self):
        """A disconnect removes whatever was blocking every barrier, so re-evaluate all of them."""
        for fn in (self._check_seed_commit_barrier, self._check_seed_reveal_barrier,
                   self._check_card_commit_barrier, self._check_card_reveal_barrier,
                   self._check_action_announce_barrier, self._check_age_end_barrier,
                   self._check_score_barrier):
            try:
                fn()
            except Exception as e:
                print(f"[!] barrier recheck error in {fn.__name__}: {type(e).__name__}: {e}")
        self._recheck_incidents()

    # ---------------- barrier watchdog (single-miss / two-miss rules) ----------------
    def _barrier_watchdog(self):
        while self.running:
            time.sleep(0.25)
            try:
                self._watchdog_tick()
            except Exception as e:
                print(f"[!] watchdog error: {type(e).__name__}: {e}")

    def _watchdog_tick(self):
        if self.spectator or not self.lobby_closed or self.aborted:
            return
        now = time.time()
        with self._turn_lock:
            # 7.5 / 11.1: a participant never heard from within T_JOIN_TIMEOUT is dropped before seeding
            # (independently observable, so no corroboration); below min_players the session aborts.
            if self.join_deadline is not None and now >= self.join_deadline:
                self.join_deadline = None
                if self.shared_seed is None:
                    for p in sorted(self.manifest):
                        if p != self.manifest_peer_id and p not in self.last_heard:
                            print(f"[!] T_JOIN_TIMEOUT: never heard from {self._pname(p)} (peer {p})")
                            self._mark_disconnected(p, "TIMEOUT")
                            if self.aborted:
                                return

            # 7.6: SEED_COMMIT / SEED_REVEAL barriers - once per session, so a SINGLE miss disconnects.
            if (self.shared_seed is None and self.seed_phase_start is not None
                    and now - self.seed_phase_start >= T_SEED_TIMEOUT):
                have = self.collected_reveals if self.manifest_peer_id in self.collected_reveals else self.collected_commits
                missing = [p for p in self._live_pids() if p not in have]
                self.seed_phase_start = now
                for p in missing:
                    print(f"[!] T_SEED_TIMEOUT: no seed message from {self._pname(p)} (peer {p})")
                    self._mark_disconnected(p, "TIMEOUT")
                    if self.aborted:
                        return

            # 7.8: CARD_COMMIT barrier - proceed without the silent peer this turn; TWO consecutive misses disconnect.
            if (self.turn_phase_start is not None and self.shared_seed is not None
                    and self.chosen_card is not None and not self.revealed_this_turn
                    and now - self.turn_phase_start >= T_TURN_TIMEOUT):
                self.turn_phase_start = now
                missing = [p for p in self._expected_peers()
                           if p != self.manifest_peer_id and p not in self.card_commits]
                for p in missing:
                    self.turn_absent.add(p)
                    self.turn_misses[p] = self.turn_misses.get(p, 0) + 1
                    print(f"[!] T_TURN_TIMEOUT: no CARD_COMMIT from {self._pname(p)} (peer {p}) "
                          f"- consecutive misses: {self.turn_misses[p]}/2")
                for p in missing:
                    if self.turn_misses[p] >= 2:
                        self._mark_disconnected(p, "TIMEOUT")
                        if self.aborted:
                            return
                self._check_card_commit_barrier()

            # 7.11: SCORE_REPORT barrier - single miss disconnects, excluded from GAME_END.
            if (self.score_phase_start is not None and not self.game_end_broadcasted
                    and now - self.score_phase_start >= T_SCORE_TIMEOUT):
                self.score_phase_start = None
                for p in [p for p in self._live_ring() if p not in self.collected_score_reports]:
                    print(f"[!] T_SCORE_TIMEOUT: no SCORE_REPORT from {self._pname(p)} (peer {p})")
                    self._mark_disconnected(p, "TIMEOUT")
                    if self.aborted:
                        return
                self._check_score_barrier()

    # ---------------- directed-failure path: incident + corroboration (7.9, 6.3) ----------------
    def _on_channel_failed(self, pid: int):
        """6.3: our channel to `pid` exhausted RETRY_MAX. Alone this does NOT disconnect it (11.3)."""
        if self.spectator or pid in self.disconnected_peers:
            return
        print(f"\n[!] CHANNEL FAILED: {self._pname(pid)} (peer {pid}) exceeded RETRY_MAX. Our sending direction to it is "
              f"now permanently closed (RFC 6.3). The peer stays LIVE unless every other live peer's channel to it "
              f"fails too (11.3). If it is a neighbour carrying HAND_PASS, this turn may stall (RFC 12.4).")
        with self._turn_lock:
            open_ids = [i for i, inc in self.incidents.items() if inc["offender"] == pid and not inc["resolved"]]
            if open_ids:
                for iid in open_ids:
                    self._echo(iid)            # our own channel has exceeded RETRY_MAX: that is our corroboration
            else:
                self._open_incident(pid, f"channel to peer {pid} exceeded RETRY_MAX")

    def _get_incident(self, iid: str, offender: int, detail: str = "") -> dict:
        inc = self.incidents.get(iid)
        if inc is None:
            inc = {"offender": offender, "reporters": set(), "echoed": False, "testing": False,
                   "resolved": False, "alive": False,
                   "detail": detail or f"peer {offender} unresponsive"}
            self.incidents[iid] = inc
        return inc

    def _open_incident(self, offender: int, detail: str):
        """7.9: fresh incident_id + ERROR{TIMEOUT} broadcast. NEVER marks the offender disconnected by itself."""
        with self._turn_lock:
            if offender == self.manifest_peer_id or offender in self.disconnected_peers:
                return
            iid = os.urandom(8).hex()
            self._get_incident(iid, offender, detail)
            self._echo(iid)

    def _echo(self, iid: str):
        """Broadcast ERROR{TIMEOUT, offending_peer, incident_id} (original report or corroboration)."""
        with self._turn_lock:
            inc = self.incidents[iid]
            if inc["echoed"] or inc["resolved"] or inc["offender"] in self.disconnected_peers:
                return
            inc["echoed"] = True
            inc["reporters"].add(self.manifest_peer_id)
            self.broadcast_error("TIMEOUT", inc["detail"], inc["offender"], incident_id=iid)
            self._check_incident(iid)

    @_turn_locked
    def _handle_error(self, sender_pid: int, payload: dict):
        if self.spectator or payload.get("code") != "TIMEOUT" or not payload.get("incident_id"):
            return
        iid = payload["incident_id"]
        seat = payload.get("offending_peer")
        if isinstance(seat, int) and self.seating_order and 0 <= seat < len(self.seating_order):
            offender = self.seating_order[seat]            # offending_peer is a SEAT (RFC 8.3)
        else:
            offender = seat
        if offender not in self.manifest or offender == self.manifest_peer_id or offender in self.disconnected_peers:
            return
        inc = self._get_incident(iid, offender, str(payload.get("detail", "")))
        inc["reporters"].add(sender_pid)
        if not inc["echoed"] and not inc["testing"]:
            if offender in self.failed_channels:
                self._echo(iid)                            # our channel already exceeded RETRY_MAX
            else:
                inc["testing"] = True
                threading.Thread(target=self._corroborate_by_ping, args=(iid,), daemon=True).start()
        self._check_incident(iid)

    def _corroborate_by_ping(self, iid: str):
        """7.9: test OUR channel to the accused with PING; re-send once after T_RESOURCE_TIMEOUT; only if
        both attempts get no PONG do we echo the SAME incident_id."""
        inc = self.incidents[iid]
        off = inc["offender"]
        addr = self.manifest.get(off)
        alive = False
        for _attempt in range(2):
            t0 = time.time()
            if addr is not None:
                self.send_unreliable(addr, MSG_PING, {"sent_at_ms": int(t0 * 1000)})
            while time.time() < t0 + T_RESOURCE_TIMEOUT:
                if self.last_pong.get(off, 0.0) >= t0:
                    alive = True
                    break
                time.sleep(0.05)
            if alive:
                break
        with self._turn_lock:
            if alive:
                inc["alive"] = True
                print(f"[*] Incident {iid[:8]}: peer {off} answered our PING - NOT corroborating (stays connected).")
                return
            self._echo(iid)

    def _check_incident(self, iid: str):
        inc = self.incidents.get(iid)
        if inc is None or inc["resolved"]:
            return
        off = inc["offender"]
        if off == self.manifest_peer_id or off in self.disconnected_peers:
            inc["resolved"] = True
            return
        needed = set(self._live_pids()) - {off}            # every OTHER live peer must have echoed this incident_id
        if needed and needed <= inc["reporters"]:
            inc["resolved"] = True
            print(f"[*] Incident {iid[:8]}: all {len(needed)} other live peers corroborated -> consensus on peer {off}.")
            # Consensus reached: broadcast DISCONNECT (best-effort, 8.1). {reason} is the RFC payload; offending_peer /
            # peer_id / incident_id are extensions (receivers ignore unknown fields) naming who the consensus is about.
            seat = self.seating_order.index(off) if off in self.seating_order else off
            self.broadcast_mesh(MSG_DISCONNECT, {"reason": "TIMEOUT", "offending_peer": seat,
                                                 "peer_id": off, "incident_id": iid}, reliable=False)
            self._mark_disconnected(off, "TIMEOUT")

    def _recheck_incidents(self):
        for iid in list(self.incidents):
            self._check_incident(iid)

    # ---------------- incoming DISCONNECT ----------------
    def _handle_disconnect(self, sender_pid: int, payload: dict):
        """DISCONNECT {reason}: the SENDER is leaving (USER_QUIT) or halting (QUORUM_LOST / PROTOCOL_VIOLATION)."""
        reason = payload.get("reason", "USER_QUIT")
        if sender_pid not in self.manifest:
            return
        if self.spectator:
            if sender_pid not in self.disconnected_peers:
                self.disconnected_peers.add(sender_pid)
                print(f"[SPECTATOR] {self._pname(sender_pid)} DISCONNECTED ({reason})")
            return
        target = self._target_from_payload(payload)
        if target is None or target == sender_pid:
            # The sender announces its OWN departure (USER_QUIT / QUORUM_LOST): no consensus needed.
            print(f"\n[!] DISCONNECT received from {self._pname(sender_pid)} (peer {sender_pid}), reason={reason}")
            self._mark_disconnected(sender_pid, reason)
            return
        if target == self.manifest_peer_id:
            # Never abort on someone else's say-so (a forged packet could kill us); just log it loudly.
            print(f"\n[!] WARNING: {self._pname(sender_pid)} (peer {sender_pid}) reports THIS node as DISCONNECTED "
                  f"({reason}). Not acting on it.")
            return
        if target in self.disconnected_peers:
            return
        # Third-party report: never adopt it blindly (11.3). If it came from a corroborated incident, join that
        # incident (test our own channel with PING); barrier-miss cases we detect ourselves.
        print(f"\n[*] {self._pname(sender_pid)} reports {self._pname(target)} DISCONNECTED ({reason}); not acting on it unilaterally.")
        iid = payload.get("incident_id")
        if isinstance(iid, str) and iid:
            seat = self.seating_order.index(target) if target in self.seating_order else target
            self._handle_error(sender_pid, {"code": "TIMEOUT", "incident_id": iid,
                                            "offending_peer": seat, "detail": "reported via DISCONNECT"})

    def _target_from_payload(self, payload: dict) -> Optional[int]:
        """Who a DISCONNECT is about: peer_id extension first, else offending_peer (a seat). None = the sender itself."""
        pid = payload.get("peer_id")
        if isinstance(pid, int) and pid in self.manifest:
            return pid
        seat = payload.get("offending_peer")
        if isinstance(seat, int):
            if self.seating_order:
                return self.seating_order[seat] if 0 <= seat < len(self.seating_order) else None
            return seat if seat in self.manifest else None
        return None

    # ---------------- RESOURCE_QUERY with 7.9 timeout discipline ----------------
    def _query_neighbors(self, pids: List[int], res: str, qty: int) -> List[int]:
        """Query, wait T_RESOURCE_TIMEOUT, re-send ONCE, wait again. Returns neighbours that never replied."""
        def replied(p: int) -> bool:
            return res in self.pending_offers.get(p, {})

        for _attempt in range(2):
            for p in pids:
                if not replied(p):
                    self.send_reliable(p, MSG_RESOURCE_QUERY, {
                        "age": self.current_age, "turn": self.current_turn, "resource": res, "quantity": qty
                    })
            deadline = time.time() + T_RESOURCE_TIMEOUT
            while time.time() < deadline and not all(replied(p) for p in pids):
                self.offer_event.clear()
                self.offer_event.wait(timeout=0.1)
            if all(replied(p) for p in pids):
                break
        return [p for p in pids if not replied(p)]

    def _retransmission_daemon(self):
        while self.running:
            now = time.time()
            to_resend = []
            to_exhaust = []
            newly_failed = []

            with self.state_lock:
                for (target_pid, seq), item in list(self.unacked_packets.items()):
                    rto = self.channel_rto.get(target_pid, RTO_INIT)
                    if now - item["last_sent"] >= rto:
                        if item["retries"] < RETRY_MAX:
                            item["retries"] += 1
                            item["last_sent"] = now
                            new_rto = min(RTO_MAX, rto * 2.0)
                            self.channel_rto[target_pid] = new_rto
                            to_resend.append(item)
                        else:
                            to_exhaust.append(((target_pid, seq), item))

                # RFC 6.3: RETRY_MAX exhausted -> this CHANNEL is failed for good. That alone does NOT
                # disconnect the peer (11.3); it is handled by _on_channel_failed() below.
                for (tp, _seq), _item in to_exhaust:
                    if tp not in self.failed_channels:
                        self.failed_channels.add(tp)
                        newly_failed.append(tp)
                for key in sorted(k for k in self.unacked_packets if k[0] in self.failed_channels):
                    if self.unacked_packets[key]["opcode"] == MSG_HAND_PASS:
                        self.lost_passes.setdefault(key[0], []).append(self.unacked_packets[key]["payload"])
                    del self.unacked_packets[key]

            for item in to_resend:
                raw_with_retx = self.pack_packet(
                    item["opcode"], item["payload"], seq=item["seq"],
                    ack=self.channel_highest_ack.get(item["target_pid"], 0),
                    flags=FLAG_RETRANSMIT
                )
                try:
                    self._raw_send(raw_with_retx, item["addr"])
                except Exception:
                    pass
                self.log("RETRY", item["addr"], item["opcode"], item["seq"], 0, FLAG_RETRANSMIT, item["payload"])

            for tp in newly_failed:
                try:
                    self._on_channel_failed(tp)
                except Exception as e:
                    print(f"[!] _on_channel_failed error: {type(e).__name__}: {e}")

            time.sleep(0.02)

    def _lobby_gossip_daemon(self):
        while self.running:
            payload = {
                "lobby_peer_id": self.lobby_peer_id,
                "display_name": self.display_name,
                "host": self.host,
                "port": self.game_port,
                "spectator": self.spectator
            }
            raw = self.pack_packet(MSG_LOBBY_PRESENCE, payload, seq=0, ack=0)
            self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_PRESENCE, 0, 0, 0, payload)

            try:
                self.lobby_sock.sendto(raw, ("<broadcast>", self.lobby_port))
            except Exception:
                pass
            try:
                self.lobby_sock.sendto(raw, ("127.0.0.1", self.lobby_port))
            except Exception:
                pass

            for target_port in (9001, 9002, 9003, 9004, 9005):
                if target_port != self.game_port:
                    try:
                        self.game_sock.sendto(raw, ("127.0.0.1", target_port))
                    except Exception:
                        pass

            now = time.time()
            with self.state_lock:
                stale = [lpid for lpid, info in self.lobby_roster.items() if now - info["last_seen"] > T_LOBBY_STALE]
                for lpid in stale:
                    del self.lobby_roster[lpid]
                    self.last_roster_change = now

            if not self.spectator and not self.lobby_closed:
                player_roster_count = sum(1 for info in self.lobby_roster.values() if not info.get("spectator", False)) + 1
                if MIN_PLAYERS <= player_roster_count <= MAX_PLAYERS:
                    if (now - self.last_roster_change >= T_LOBBY_QUIET) or (now - self.seeking_start_time >= T_LOBBY_TIMEOUT):
                        self._propose_lobby_start()

            time.sleep(T_LOBBY_ANNOUNCE_INTERVAL)

    def _propose_lobby_start(self):
        player_lpids = [lpid for lpid, info in self.lobby_roster.items() if not info.get("spectator", False)]
        player_lpids.append(self.lobby_peer_id)
        sorted_participants = sorted(player_lpids)

        payload = {"participants": sorted_participants}
        raw = self.pack_packet(MSG_LOBBY_START_VOTE, payload)
        self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_START_VOTE, 0, 0, 0, payload)

        targets = [("<broadcast>", self.lobby_port), ("127.0.0.1", self.lobby_port)]
        for info in self.lobby_roster.values():
            targets.append((info["host"], info["port"]))
        for s_addr in self.spectator_addrs:
            targets.append(s_addr)

        for dest in targets:
            try:
                self.game_sock.sendto(raw, dest)
            except Exception:
                pass

    def _handle_presence_packet(self, payload: dict, addr: Tuple[str, int]):
        lpid = payload.get("lobby_peer_id")
        if not lpid or lpid == self.lobby_peer_id:
            return

        is_spec = payload.get("spectator", False)
        with self.state_lock:
            if is_spec:
                spec_tuple = (payload.get("host", addr[0]), payload.get("port", addr[1]))
                if spec_tuple not in self.spectator_addrs:
                    self.spectator_addrs.add(spec_tuple)
                    print(f"[*] Spectator Connected: '{payload['display_name']}' @ {spec_tuple[0]}:{spec_tuple[1]}")
                    if self.shared_seed is not None and not self.spectator:
                        sync_data = {
                            "seating_order": self.seating_order,
                            "manifest_names": self.manifest_names,
                            "all_wonders": self.all_wonders,
                            "public_tableaus": self.public_tableaus,
                            "age": self.current_age,
                            "turn": self.current_turn
                        }
                        self.send_unreliable(spec_tuple, MSG_SPECTATOR_SYNC, sync_data)
            else:
                if lpid not in self.lobby_roster:
                    self.last_roster_change = time.time()
                    if not self.lobby_closed:
                        print(f"[*] Discovered Player: '{payload['display_name']}' ({payload['host']}:{payload['port']})")
                self.lobby_roster[lpid] = {
                    "display_name": payload["display_name"],
                    "host": payload["host"],
                    "port": payload["port"],
                    "spectator": False,
                    "last_seen": time.time()
                }

    def _handle_lobby_packet(self, opcode: int, payload: dict, addr: Tuple[str, int]):
        if opcode == MSG_LOBBY_PRESENCE:
            self._handle_presence_packet(payload, addr)

        elif opcode == MSG_LOBBY_LEAVE and not self.lobby_closed:
            lpid = payload.get("lobby_peer_id")
            with self.state_lock:
                if lpid and lpid in self.lobby_roster:
                    del self.lobby_roster[lpid]
                    self.last_roster_change = time.time()

        elif opcode == MSG_LOBBY_START_VOTE and not self.lobby_closed:
            proposed = payload.get("participants", [])
            if self.spectator:
                self._finalize_lobby_and_start(proposed)
                return

            player_lpids = [lpid for lpid, info in self.lobby_roster.items() if not info.get("spectator", False)]
            player_lpids.append(self.lobby_peer_id)
            my_full_roster = sorted(player_lpids)

            if proposed == my_full_roster:
                p_hash = sha256_hex(json.dumps(proposed).encode("utf-8"))
                ack_payload = {
                    "lobby_peer_id": self.lobby_peer_id,
                    "participants_hash": p_hash
                }
                ack_pkt = self.pack_packet(MSG_LOBBY_START_ACK, ack_payload)
                self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_START_ACK, 0, 0, 0, ack_payload)

                targets = [("<broadcast>", self.lobby_port), ("127.0.0.1", self.lobby_port)]
                for info in self.lobby_roster.values():
                    targets.append((info["host"], info["port"]))
                for s_addr in self.spectator_addrs:
                    targets.append(s_addr)

                for dest in targets:
                    try:
                        self.game_sock.sendto(ack_pkt, dest)
                    except Exception:
                        pass

                self.collected_start_acks.add(self.lobby_peer_id)
                if len(self.collected_start_acks) >= len(my_full_roster):
                    self._finalize_lobby_and_start(my_full_roster)

        elif opcode == MSG_LOBBY_START_ACK and not self.lobby_closed:
            if self.spectator:
                return
            player_lpids = [lpid for lpid, info in self.lobby_roster.items() if not info.get("spectator", False)]
            player_lpids.append(self.lobby_peer_id)
            my_full_roster = sorted(player_lpids)
            expected_hash = sha256_hex(json.dumps(my_full_roster).encode("utf-8"))

            if payload.get("participants_hash") == expected_hash:
                ack_sender_lpid = payload.get("lobby_peer_id")
                if ack_sender_lpid:
                    self.collected_start_acks.add(ack_sender_lpid)
                else:
                    self.collected_start_acks.add(addr[0] + ":" + str(addr[1]))

                if len(self.collected_start_acks) >= len(my_full_roster):
                    self._finalize_lobby_and_start(my_full_roster)

    def _lobby_listener(self):
        while self.running:
            try:
                data, addr = self.lobby_sock.recvfrom(65535)
                opcode, flags, sender_pid, sess_id, plen, seq, ack, payload = self.unpack_packet(data)
                if sess_id != self.session_id:
                    continue
                if not (opcode == MSG_LOBBY_PRESENCE and payload.get("lobby_peer_id") == self.lobby_peer_id):
                    self.log("RECV", addr, opcode, seq, ack, flags, payload)
                self._handle_lobby_packet(opcode, payload, addr)
            except Exception:
                pass

    def _finalize_lobby_and_start(self, participants: List[str]):
        if self.lobby_closed:
            return
        self.lobby_closed = True

        for rank, lpid in enumerate(participants, start=1):
            if lpid == self.lobby_peer_id and not self.spectator:
                self.manifest_peer_id = rank
                self.manifest[rank] = (self.host, self.game_port)
                self.manifest_names[rank] = self.display_name
                self.hello_acks_received.add(rank)
            else:
                pinfo = self.lobby_roster.get(lpid)
                if pinfo:
                    self.manifest[rank] = (pinfo["host"], pinfo["port"])
                    self.manifest_names[rank] = pinfo["display_name"]
                else:
                    self.manifest[rank] = ("127.0.0.1", 9000 + rank)
                    self.manifest_names[rank] = f"Player_{rank}"

        role = "SPECTATOR" if self.spectator else f"PLAYER {self.manifest_peer_id}"
        print(f"\n=======================================================")
        print(f" [+] SESSION STARTED! Role: {role}")
        for pid, addr in self.manifest.items():
            print(f"     Player {pid}: {self.manifest_names[pid]} @ {addr[0]}:{addr[1]}")
        print(f"=======================================================\n")

        if not self.spectator:
            self.join_deadline = time.time() + T_JOIN_TIMEOUT
            for pid in self.manifest:
                if pid != self.manifest_peer_id:
                    self.send_reliable(pid, MSG_HELLO, {})
        else:
            print("[SPECTATOR] Live monitoring active. Waiting for game to start...\n")

    def start_seed_ceremony(self):
        if self.spectator:
            return
        if self.manifest_peer_id in self.collected_commits:
            return
        print("\n[*] Randomness Ceremony initiated...")
        self.collected_commits[self.manifest_peer_id] = self.my_commitment
        self.seed_phase_start = time.time()
        self.broadcast_mesh(MSG_SEED_COMMIT, {"commitment": self.my_commitment})
        self._check_seed_commit_barrier()

    def _handle_seed_commit(self, sender_pid: int, payload: dict):
        self.collected_commits[sender_pid] = payload["commitment"]
        if sender_pid in self.pending_seed_reveals:      # its reveal overtook it: verify now
            self._handle_seed_reveal(sender_pid, {"nonce": self.pending_seed_reveals.pop(sender_pid).hex()})
        if not self.spectator and self.manifest_peer_id not in self.collected_commits:
            self.start_seed_ceremony()
        self._check_seed_commit_barrier()

    @_turn_locked
    def _check_seed_commit_barrier(self):
        if not self.spectator and set(self._live_pids()) <= set(self.collected_commits):
            if self.manifest_peer_id not in self.collected_reveals:
                self.seed_phase_start = time.time()      # start the SEED_REVEAL window (T_SEED_TIMEOUT)
                self.collected_reveals[self.manifest_peer_id] = self.my_nonce
                self.broadcast_mesh(MSG_SEED_REVEAL, {"nonce": self.my_nonce.hex()})
                self._check_seed_reveal_barrier()

    def _handle_seed_reveal(self, sender_pid: int, payload: dict):
        nonce_bytes = bytes.fromhex(payload["nonce"])
        expected_commit = self.collected_commits.get(sender_pid)
        if not expected_commit:
            # The SEED_COMMIT was lost/reordered and has not arrived yet: hold the reveal and verify it later
            self.pending_seed_reveals[sender_pid] = nonce_bytes
            return
        if sha256_hex(nonce_bytes) != expected_commit:
            self.broadcast_error("COMMITMENT_MISMATCH", f"SEED_REVEAL mismatch from peer {sender_pid}", sender_pid)
            # 7.6 step 3 / 11.3: broadcast-observable -> every peer disconnects it independently, no corroboration.
            self._mark_disconnected(sender_pid, "PROTOCOL_VIOLATION")
            return
        self.collected_reveals[sender_pid] = nonce_bytes
        self._check_seed_reveal_barrier()

    @_turn_locked
    def _check_seed_reveal_barrier(self):
        live_pids = self._live_pids()
        if live_pids and set(live_pids) <= set(self.collected_reveals) and self.shared_seed is None:
            # 7.6: n_i concatenated only over SURVIVING peers, ascending Sender Peer ID
            concat_nonces = b"".join(self.collected_reveals[pid] for pid in live_pids)
            self.shared_seed = sha256_hash(concat_nonces)
            self.seed_phase_start = None

            self.seating_order = self.card_engine.derive_ring_seating(self.shared_seed, live_pids)
            self.all_wonders = self.card_engine.assign_wonders(self.shared_seed, self.seating_order)
            self.selected_guilds = [
                g["card_id"] for g in self.card_engine.select_guild_cards(self.shared_seed, len(self.seating_order))
            ]

            for pid in self.seating_order:
                self.public_tableaus[pid] = {
                    "coins": 3,
                    "built_cards": [],
                    "wonder_stages_built": 0,
                    "military_tokens": [],
                    "science_symbols": [],
                    "wonder_board": self.all_wonders[pid]
                }

            if not self.spectator:
                self.my_seat = self.seating_order.index(self.manifest_peer_id)
                self.my_wonder_board = self.all_wonders[self.manifest_peer_id]
                self.resources[self.my_wonder_board["starting_resource"]] += 1
                self.broadcast_mesh(MSG_RING_CONFIRM, {
                    "seat": self.my_seat,
                    "seating_order": self.seating_order,
                    "wonder_board": self.my_wonder_board["board"],
                    "wonder_side": self.my_wonder_board["side"],
                    "guilds": self.selected_guilds
                })
                self._deal_age(1)
            else:
                print("\n[SPECTATOR] Randomness Ceremony complete! Ring and Wonder boards derived:")
                for s_idx, pid in enumerate(self.seating_order):
                    pname = self.manifest_names.get(pid, f"Player {pid}")
                    wb = self.all_wonders[pid]
                    print(f"  Seat {s_idx}: {pname:<10} | Wonder: {wb['board']} (Side {wb['side']}) | Starts with {wb['starting_resource']}")
                print("\n[SPECTATOR] Age 1 has begun! Live monitoring card drafts...\n")

    def _handle_ring_confirm(self, sender_pid: int, payload: dict):
        if self.shared_seed is None:
            return
        expected_seat = self.seating_order.index(sender_pid) if sender_pid in self.seating_order else -1
        expected_wb = self.all_wonders.get(sender_pid, {})
        if (payload.get("seat") != expected_seat or
                payload.get("wonder_board") != expected_wb.get("board") or
                payload.get("wonder_side") != expected_wb.get("side") or
                payload.get("seating_order", self.seating_order) != self.seating_order or
                payload.get("guilds", self.selected_guilds) != self.selected_guilds):
            self.broadcast_error("RING_MISMATCH", f"RING_CONFIRM mismatch from peer {sender_pid}", sender_pid)

    def _deal_age(self, age: int):
        self.current_age = age
        self.current_turn = 1
        self.revealed_this_turn = False
        self.announced_this_turn = False
        self.resources_bought_this_turn.clear()
        self.my_pass_sent = False
        self.inbound_hands = [h for h in self.inbound_hands if h.get("age", 0) >= age]
        full_deck = self.card_engine.build_age_deck(self.shared_seed, age, len(self.seating_order))
        self.current_hand = full_deck[self.my_seat * 7 : (self.my_seat + 1) * 7]
        print(f"\n=======================================================")
        print(f"                AGE {age} HAS COMMENCED")
        print(f"=======================================================")
        self._display_hand()

    def _display_hand(self):
        print(f"\n--- Age {self.current_age} | Turn {self.current_turn} / 6 (Seat {self.my_seat}: {self.display_name}) ---")
        res_str = ", ".join(f"{k}:{v}" for k, v in self.resources.items() if v > 0)
        print(f"Coins: {self.coins} | Shields: {self.military_shields} | Production: [{res_str}]")
        print(f"Cards in Hand ({len(self.current_hand)}):")
        for idx, card in enumerate(self.current_hand):
            print(f"  {idx}: {card['name']:<20} | Color: {card['color']:<6} | Cost: {card['cost']:<14} | Chain: {card['chain_from']}")
        print("To act: type 'pick <index> [BUILD / DISCARD / WONDER]'")

    def trade_resource(self, direction: str, resource: str):
        if self.spectator or not self.seating_order:
            return
        offset = -1 if direction.lower() == "left" else 1
        target_pid = self._neighbor_pid(offset)
        res_key = resource.upper()
        self.send_reliable(target_pid, MSG_RESOURCE_QUERY, {
            "age": self.current_age,
            "turn": self.current_turn,
            "resource": res_key,
            "quantity": 1
        })

    def _handle_resource_query(self, sender_pid: int, payload: dict):
        res_key = payload.get("resource", "").upper()
        qty = int(payload.get("quantity", 1))
        avail = min(qty, self.resources.get(res_key, 0))
        self.send_reliable(sender_pid, MSG_RESOURCE_OFFER, {
            "age": self.current_age,
            "turn": self.current_turn,
            "resource": res_key,
            "available": avail
        })

    def _handle_resource_offer(self, sender_pid: int, payload: dict):
        res_key = payload.get("resource", "").upper()
        avail = int(payload.get("available", 0))
        self.pending_offers.setdefault(sender_pid, {})[res_key] = avail
        self.offer_event.set()

        if not self.revealed_this_turn and avail > 0:
            left_pid = self._neighbor_pid(-1)
            is_mfg = res_key in ("GLASS", "PAPYRUS", "TEXTILE")
            unit_price = self.trade_discounts["mfg"] if is_mfg else (
                self.trade_discounts["raw_left"] if sender_pid == left_pid else self.trade_discounts["raw_right"]
            )
            if self.coins >= unit_price:
                self.coins -= unit_price
                self.resources_bought_this_turn.append({
                    "peer_id": sender_pid, "resource": res_key, "quantity": 1, "coins_paid": unit_price
                })
                self.send_reliable(sender_pid, MSG_RESOURCE_BUY, {
                    "age": self.current_age,
                    "turn": self.current_turn,
                    "resource": res_key,
                    "quantity": 1,
                    "coins_paid": unit_price
                })

    def _handle_resource_buy(self, sender_pid: int, payload: dict):
        paid = int(payload.get("coins_paid", 0))
        self.coins += paid
        if self.manifest_peer_id in self.public_tableaus:
            self.public_tableaus[self.manifest_peer_id]["coins"] = self.coins
        if sender_pid in self.public_tableaus:
            self.public_tableaus[sender_pid]["coins"] = self.public_tableaus[sender_pid].get("coins", 3) - paid

    def draft_action(self, card_idx: int, action: str = "BUILD"):
        if self.spectator:
            print("[SPECTATOR] Spectators cannot draft cards.")
            return
        if card_idx < 0 or card_idx >= len(self.current_hand):
            print("Invalid card selection.")
            return

        act = action.upper()
        if act == "WONDER":
            act = "WONDER_STAGE"
        if act not in ("BUILD", "WONDER_STAGE", "DISCARD"):
            print("[!] Action must be BUILD, DISCARD or WONDER.")
            return

        card = self.current_hand[card_idx]
        self.chosen_card = card
        self.chosen_action = act
        self.chosen_nonce = os.urandom(32)

        token = card["card_id"].encode("utf-8") + self.chosen_action.encode("utf-8") + self.chosen_nonce
        commit_digest = sha256_hex(token)

        self.card_commits[self.manifest_peer_id] = commit_digest
        self.turn_phase_start = time.time()      # start the T_TURN_TIMEOUT CARD_COMMIT window
        print(f"[*] Committed {self.chosen_action} on '{card['name']}'. Waiting for other players...")

        self.broadcast_mesh(MSG_CARD_COMMIT, {
            "age": self.current_age,
            "turn": self.current_turn,
            "commitment": commit_digest
        })
        self._check_card_commit_barrier()

    @_turn_locked
    def _handle_card_commit(self, sender_pid: int, payload: dict):
        self.card_commits[sender_pid] = payload["commitment"]
        if sender_pid not in self.turn_absent:
            self.turn_misses[sender_pid] = 0     # 11.3: only CONSECUTIVE misses count
        early = self.pending_card_reveals.pop(sender_pid, None)
        if early is not None:                              # its reveal overtook it: verify now
            self._handle_card_reveal(sender_pid, early)
        self._check_card_commit_barrier()

    @_turn_locked
    def _check_card_commit_barrier(self):
        if not self.spectator and self.chosen_card is not None and not self.revealed_this_turn:
            if self._expected_peers() <= set(self.card_commits):
                self.revealed_this_turn = True
                self.turn_phase_start = None
                reveal_payload = {
                    "age": self.current_age,
                    "turn": self.current_turn,
                    "action": self.chosen_action,
                    "nonce": self.chosen_nonce.hex()
                }
                if self.chosen_action == "BUILD":
                    reveal_payload["card_id"] = self.chosen_card["card_id"]

                self.broadcast_mesh(MSG_CARD_REVEAL, reveal_payload)
                self.card_reveals[self.manifest_peer_id] = reveal_payload
                self._check_card_reveal_barrier()

    @_turn_locked
    def _handle_card_reveal(self, sender_pid: int, payload: dict):
        expected_commit = self.card_commits.get(sender_pid)
        cid = payload.get("card_id", "")
        act = payload.get("action", "")
        nonce_bytes = bytes.fromhex(payload.get("nonce", ""))
        if not expected_commit and not self.spectator:
            self.pending_card_reveals[sender_pid] = payload   # commit not here yet: verify once it arrives
            return
        if expected_commit and cid:
            token = cid.encode("utf-8") + act.encode("utf-8") + nonce_bytes
            if sha256_hex(token) != expected_commit:
                self.broadcast_error("COMMITMENT_MISMATCH", f"CARD_REVEAL mismatch from peer {sender_pid}", sender_pid)
                return
        self.card_reveals[sender_pid] = payload
        self._check_card_reveal_barrier()

    @_turn_locked
    def _check_card_reveal_barrier(self):
        if not self.spectator and self.revealed_this_turn and not self.announced_this_turn:
            if self._expected_peers() <= set(self.card_reveals):
                self.announced_this_turn = True
                threading.Thread(target=self._execute_resolve_and_announce, daemon=True).start()

    def _acquire_missing_resources(self, res_req: Dict[str, int], coins_req: int) -> bool:
        bought_counts = {r: 0 for r in RESOURCE_KEYS}
        for b in self.resources_bought_this_turn:
            bought_counts[b["resource"]] = bought_counts.get(b["resource"], 0) + b["quantity"]

        deficit = {
            r: max(0, amt - self.resources.get(r, 0) - bought_counts.get(r, 0))
            for r, amt in res_req.items()
        }
        if sum(deficit.values()) == 0:
            return self.coins >= coins_req

        left_pid = self._neighbor_pid(-1)
        right_pid = self._neighbor_pid(+1)
        self.pending_offers.clear()

        for r, need in deficit.items():
            if need > 0:
                queried = [p for p in dict.fromkeys((left_pid, right_pid))
                           if p != self.manifest_peer_id
                           and p not in self.failed_channels and p not in self.disconnected_peers]
                silent = self._query_neighbors(queried, r, need)
                for sp in silent:
                    # 7.9: private, directed timeout -> open an incident; NEVER disconnect unilaterally.
                    self._open_incident(sp, f"no RESOURCE_OFFER for {r} within T_RESOURCE_TIMEOUT (after one re-send)")

                is_mfg = r in ("GLASS", "PAPYRUS", "TEXTILE")
                neighbors = sorted(
                    [(left_pid, self.trade_discounts["mfg"] if is_mfg else self.trade_discounts["raw_left"]),
                     (right_pid, self.trade_discounts["mfg"] if is_mfg else self.trade_discounts["raw_right"])],
                    key=lambda x: x[1]
                )
                rem = need
                for npid, uprice in neighbors:
                    avail = self.pending_offers.get(npid, {}).get(r, 0)
                    take = min(rem, avail)
                    if take > 0 and (self.coins - coins_req) >= take * uprice:
                        paid = take * uprice
                        self.coins -= paid
                        rem -= take
                        self.resources_bought_this_turn.append({"peer_id": npid, "resource": r, "quantity": take, "coins_paid": paid})
                        self.send_reliable(npid, MSG_RESOURCE_BUY, {
                            "age": self.current_age, "turn": self.current_turn,
                            "resource": r, "quantity": take, "coins_paid": paid
                        })
                if rem > 0:
                    return False
        return self.coins >= coins_req

    def _execute_resolve_and_announce(self):
        card = self.chosen_card
        action = self.chosen_action
        self.current_hand = [c for c in self.current_hand if c["instance_id"] != card["instance_id"]]

        if action == "BUILD":
            coins_req, res_req = parse_card_cost(card["cost"])
            is_chained = verify_chaining(card, self.built_cards)
            if not is_chained and not self._acquire_missing_resources(res_req, coins_req):
                action = "DISCARD"

        announce_payload = {
            "action": action,
            "age": self.current_age,
            "turn": self.current_turn,
            "peer_name": self.display_name
        }

        if action == "BUILD":
            coins_req, _ = parse_card_cost(card["cost"])
            is_chained = verify_chaining(card, self.built_cards)
            cost_paid = {
                "coins": 0 if is_chained else coins_req,
                "resources_bought": list(self.resources_bought_this_turn)
            }

            self.coins -= cost_paid["coins"]
            self.built_cards.append(card)
            self._apply_card_effects(card)

            announce_payload["card_id"] = card["card_id"]
            announce_payload["cost_paid"] = cost_paid

        elif action == "WONDER_STAGE":
            self.wonder_stages_built += 1
            announce_payload["stage_index"] = self.wonder_stages_built

        elif action == "DISCARD":
            self.coins += 3

        self.resources_bought_this_turn.clear()
        self.action_announcements[self.manifest_peer_id] = announce_payload
        self.broadcast_mesh(MSG_ACTION_ANNOUNCE, announce_payload)
        self._check_action_announce_barrier()

    def _apply_card_effects(self, card: Dict[str, Any]):
        eff = card.get("effect", "")
        color = card.get("color", "")
        if color == "RED":
            shields = 1 if "1 Shield" in eff else 2 if "2 Shields" in eff else 3
            self.military_shields += shields
        elif color in ("BROWN", "GREY"):
            for r in RESOURCE_KEYS:
                if f"Produces 1 {r.capitalize()}" in eff or f"Produces 1 {r}" in eff:
                    self.resources[r] += 1
        elif color == "YELLOW":
            if "3 coins" in eff:
                self.coins += 3
            elif "West Trading Post" in card["name"]:
                self.trade_discounts["raw_left"] = 1
            elif "East Trading Post" in card["name"]:
                self.trade_discounts["raw_right"] = 1
            elif "Marketplace" in card["name"]:
                self.trade_discounts["mfg"] = 1
        elif color == "GREEN":
            sym = "TABLET" if "Tablet" in eff else "COMPASS" if "Compass" in eff else "GEAR"
            self.science_symbols.append(sym)

    @_turn_locked
    def _handle_action_announce(self, sender_pid: int, payload: dict):
        self.action_announcements[sender_pid] = payload
        act = payload.get("action")
        sender_name = payload.get("peer_name", self.manifest_names.get(sender_pid, f"Player {sender_pid}"))
        self.manifest_names[sender_pid] = sender_name

        tab = self.public_tableaus.setdefault(sender_pid, {
            "built_cards": [], "coins": 3, "wonder_stages_built": 0,
            "military_tokens": [], "science_symbols": []
        })
        if act == "BUILD":
            cid = payload.get("card_id")
            card_obj = self.card_engine.lookup_card(cid) or {"card_id": cid, "color": "UNKNOWN", "effect": ""}
            cost_paid = payload.get("cost_paid", {})
            tab["coins"] = tab.get("coins", 3) - int(cost_paid.get("coins", 0))
            if card_obj.get("color") == "YELLOW" and "3 coins" in card_obj.get("effect", ""):
                tab["coins"] += 3
            elif card_obj.get("color") == "GREEN":
                eff = card_obj.get("effect", "")
                sym = "TABLET" if "Tablet" in eff else "COMPASS" if "Compass" in eff else "GEAR"
                tab.setdefault("science_symbols", []).append(sym)
            tab["built_cards"].append(card_obj)
            if self.spectator:
                print(f"[TURN {payload.get('turn')}] {sender_name} BUILT: '{cid}'")
        elif act == "WONDER_STAGE":
            tab["wonder_stages_built"] += 1
            if self.spectator:
                print(f"[TURN {payload.get('turn')}] {sender_name} BUILT WONDER STAGE {tab['wonder_stages_built']}")
        elif act == "DISCARD":
            tab["coins"] += 3
            if self.spectator:
                print(f"[TURN {payload.get('turn')}] {sender_name} DISCARDED for 3 coins")

        self._check_action_announce_barrier()

    @_turn_locked
    def _check_action_announce_barrier(self):
        if (not self.spectator and self.manifest_peer_id in self.action_announcements
                and self._expected_peers() <= set(self.action_announcements)):
            self._finalize_turn_and_pass()

    def _finalize_turn_and_pass(self):
        self.card_commits.clear()
        self.card_reveals.clear()
        self.pending_card_reveals.clear()
        self.action_announcements.clear()
        self.turn_absent.clear()
        self.turn_phase_start = None
        self.chosen_card = None
        self.revealed_this_turn = False
        self.announced_this_turn = False

        direction = -1 if self.current_age in (1, 3) else 1
        target_pid = self._neighbor_pid(direction)      # 11.3: disconnected seats are skipped

        if self.current_turn == 6:
            print(f"\n[*] Turn 6 finished. Unplayed card silently set aside.")
            self.current_hand.clear()
            self.send_reliable(target_pid, MSG_HAND_PASS, {
                "age": self.current_age, "turn": 6, "cards": []
            })
            self._resolve_military_age_end()
            return

        pass_payload = {
            "age": self.current_age,
            "turn": self.current_turn,
            "cards": [c["card_id"] for c in self.current_hand]
        }
        self.send_reliable(target_pid, MSG_HAND_PASS, pass_payload)
        self.last_pass = (target_pid, pass_payload)
        self.my_pass_sent = True
        self._try_advance_turn()

    @_turn_locked
    def _handle_hand_pass(self, sender_pid: int, payload: dict):
        if self.spectator: return
        if payload.get("turn") == 6:
            return
        # RFC 7.8 step 6: do NOT start the next turn until my own turn is finished and my own pass is sent.
        # A fast neighbour's hand can arrive while I am still resolving (e.g. waiting on a trade), so hold it.
        key = (payload.get("age"), payload.get("turn"))
        if any((h.get("age"), h.get("turn")) == key for h in self.inbound_hands):
            return                                   # duplicate (e.g. original + re-routed copy)
        self.inbound_hands.append(payload)
        self._try_advance_turn()

    @_turn_locked
    def _try_advance_turn(self):
        if not self.my_pass_sent:
            return
        match = [h for h in self.inbound_hands
                 if h.get("age") == self.current_age and h.get("turn") == self.current_turn]
        if not match:
            return
        payload = match[0]
        self.inbound_hands.remove(payload)
        self.my_pass_sent = False
        cids = payload.get("cards", [])
        new_hand = []
        for cid in cids:
            card = self.card_engine.lookup_card(cid)
            if card is None:
                print(f"[!] HAND_PASS contained unknown card_id '{cid}'")
                continue
            card["instance_id"] = f"{cid}_{os.urandom(4).hex()}"
            new_hand.append(card)

        self.current_hand = new_hand
        self.current_turn += 1
        self._display_hand()

    def _resolve_military_age_end(self):
        print(f"\n[*] Broadcasting military shields for Age {self.current_age} resolution...")
        self.age_end_shields[self.manifest_peer_id] = self.military_shields
        self.broadcast_mesh(MSG_AGE_END, {
            "age": self.current_age,
            "shields": self.military_shields,
            "peer_name": self.display_name
        })
        self._check_age_end_barrier()

    @_turn_locked
    def _handle_age_end(self, sender_pid: int, payload: dict):
        self.age_end_shields[sender_pid] = payload["shields"]

        if self.spectator and len(self.age_end_shields) == len(self.seating_order):
            print(f"\n[SPECTATOR] Age {payload.get('age')} Ended! Military Results:")
            for pid, sh in self.age_end_shields.items():
                pname = self.manifest_names.get(pid, f"Player {pid}")
                print(f"  {pname}: {sh} shields")
            self.age_end_shields.clear()

        self._check_age_end_barrier()

    @_turn_locked
    def _check_age_end_barrier(self):
        live = self._live_ring()
        if (not self.spectator and live and set(live) <= set(self.age_end_shields)
                and self.manifest_peer_id in self.age_end_shields):
            k = len(live)          # disconnected peers are excluded from military comparisons (11.3)
            win_vp = 1 if self.current_age == 1 else 3 if self.current_age == 2 else 5

            for seat_idx, pid in enumerate(live):
                l_pid = live[(seat_idx - 1) % k]
                r_pid = live[(seat_idx + 1) % k]
                toks = self.public_tableaus[pid].setdefault("military_tokens", [])
                if self.age_end_shields[pid] > self.age_end_shields[l_pid]:
                    toks.append(win_vp)
                elif self.age_end_shields[pid] < self.age_end_shields[l_pid]:
                    toks.append(-1)
                if self.age_end_shields[pid] > self.age_end_shields[r_pid]:
                    toks.append(win_vp)
                elif self.age_end_shields[pid] < self.age_end_shields[r_pid]:
                    toks.append(-1)

            self.military_tokens = list(self.public_tableaus[self.manifest_peer_id]["military_tokens"])
            self.age_end_shields.clear()
            if self.current_age < 3:
                self._deal_age(self.current_age + 1)
            else:
                self._compute_and_broadcast_scores()

    def _compute_and_broadcast_scores(self):
        print("\n[*] Game End: Computing 7-category independent final scores (RFC 7.11)...")
        self.public_tableaus[self.manifest_peer_id] = {
            "coins": self.coins,
            "military_tokens": self.military_tokens,
            "wonder_stages_built": self.wonder_stages_built,
            "built_cards": self.built_cards,
            "science_symbols": self.science_symbols,
            "wonder_board": self.my_wonder_board
        }

        all_computed = compute_all_scores(self._live_ring(), self.public_tableaus)
        my_report = all_computed[self.manifest_peer_id]
        self.collected_score_reports[self.manifest_peer_id] = my_report
        self.broadcast_mesh(MSG_SCORE_REPORT, my_report)
        self.score_phase_start = time.time()     # start the T_SCORE_TIMEOUT window
        self._check_score_barrier()

    @_turn_locked
    def _handle_score_report(self, sender_pid: int, payload: dict):
        self.collected_score_reports[sender_pid] = payload
        self._check_score_barrier()

    @_turn_locked
    def _check_score_barrier(self):
        live = self._live_ring()
        if (live and set(live) <= set(self.collected_score_reports) and not self.game_end_broadcasted
                and (self.spectator or self.manifest_peer_id in self.collected_score_reports)):
            # disconnected peers are excluded from the cross-check and from GAME_END's final_scores (7.11)
            reports = {p: r for p, r in self.collected_score_reports.items() if p in live}
            if not self.spectator:
                expected_all = compute_all_scores(live, self.public_tableaus)
                cats = ("military", "wonder", "civilian", "scientific", "commercial", "guilds")
                for pid, reported in reports.items():
                    exp = expected_all.get(pid, {})
                    bad = [c for c in cats if reported.get(c) != exp.get(c)]
                    if sum(reported.get(c, 0) for c in cats + ("treasury",)) != reported.get("total"):
                        bad.append("total != sum of categories")
                    if bad:
                        self.broadcast_error("SCORE_MISMATCH", f"SCORE_REPORT mismatch from peer {pid}: {bad}", pid)
                        return

            self.game_end_broadcasted = True
            print("\n======================= FINAL SCOREBOARD =======================")
            ranked = []
            for pid, sc in reports.items():
                ranked.append((pid, sc["total"], self.public_tableaus[pid].get("coins", 0), sc))
            ranked.sort(key=lambda x: (x[1], x[2]), reverse=True)

            for rank, (pid, tot, c, sc) in enumerate(ranked, start=1):
                pname = self.manifest_names.get(pid, f"Player {pid}")
                print(f"Rank {rank}: {pname:<12} (Seat {self.seating_order.index(pid)}) | Score: {tot:2} VP | Coins: {c} | Breakdown: {sc}")
            print("================================================================\n")

            if not self.spectator:
                winner_pid = ranked[0][0]
                winner_seat = self.seating_order.index(winner_pid)
                final_scores_payload = [
                    {"seat": self.seating_order.index(p), "total": s["total"], "coins": self.public_tableaus[p].get("coins", 0)}
                    for p, s in reports.items()
                ]
                self.broadcast_mesh(MSG_GAME_END, {
                    "winner_seat": winner_seat,
                    "final_scores": final_scores_payload
                })

    def print_spectator_dashboard(self):
        print("\n================ LIVE SPECTATOR DASHBOARD ================")
        display_pids = self.seating_order if self.seating_order else sorted(list(self.public_tableaus.keys()))
        if not display_pids and self.manifest:
            display_pids = sorted(list(self.manifest.keys()))

        if not display_pids:
            print("No player data received yet.")
            print("==========================================================\n")
            return

        for pid in display_pids:
            pname = self.manifest_names.get(pid, f"Player {pid}")
            tab = self.public_tableaus.get(pid, {})
            b_cnt = len(tab.get("built_cards", []))
            w_st = tab.get("wonder_stages_built", 0)
            c = tab.get("coins", 3)
            seat_str = f"Seat {self.seating_order.index(pid)}" if (self.seating_order and pid in self.seating_order) else f"Player {pid}"
            print(f"{seat_str:<10}: {pname:<10} | Built Structures: {b_cnt:2} | Wonder Stages: {w_st} | Coins: {c}")
        print("==========================================================\n")

    def _game_listener(self):
        while self.running:
            try:
                data, addr = self.game_sock.recvfrom(65535)
                opcode, flags, sender_pid, sess_id, plen, seq, ack, payload = self.unpack_packet(data)
                self.log("RECV", addr, opcode, seq, ack, flags, payload)
                if sender_pid in self.manifest:
                    self.last_heard[sender_pid] = time.time()

                if flags & FLAG_ACK and ack > 0:
                    with self.state_lock:
                        if (sender_pid, ack) in self.unacked_packets:
                            del self.unacked_packets[(sender_pid, ack)]
                            self.channel_rto[sender_pid] = self.channel_rto_base.get(sender_pid, RTO_INIT)

                if opcode not in UNRELIABLE_MESSAGES and seq > 0 and not self.spectator:
                    with self.state_lock:
                        self.channel_highest_ack[sender_pid] = max(
                            self.channel_highest_ack.get(sender_pid, 0), seq
                        )
                        if seq in self.delivered_seqs.setdefault(sender_pid, set()):
                            self.send_bare_ack(sender_pid, seq)
                            continue
                        self.delivered_seqs[sender_pid].add(seq)
                    self.send_bare_ack(sender_pid, seq)

                if sender_pid in self.disconnected_peers and opcode != MSG_DISCONNECT:
                    continue   # RFC 11.3: a peer marked DISCONNECTED is excluded from the session
                if opcode in (MSG_LOBBY_PRESENCE, MSG_LOBBY_LEAVE, MSG_LOBBY_START_VOTE, MSG_LOBBY_START_ACK):
                    self._handle_lobby_packet(opcode, payload, addr)
                elif opcode == MSG_SPECTATOR_SYNC and self.spectator:
                    self.seating_order = payload.get("seating_order", [])
                    self.manifest_names = {int(k): v for k, v in payload.get("manifest_names", {}).items()}
                    self.all_wonders = {int(k): v for k, v in payload.get("all_wonders", {}).items()}
                    self.public_tableaus = {int(k): v for k, v in payload.get("public_tableaus", {}).items()}
                    self.current_age = payload.get("age", 1)
                    self.current_turn = payload.get("turn", 1)
                    self.lobby_closed = True
                    print(f"\n[SPECTATOR] Synchronized with live game! (Age {self.current_age}, Turn {self.current_turn})")
                    self.print_spectator_dashboard()
                elif opcode == MSG_HELLO and not self.spectator:
                    self.send_reliable(sender_pid, MSG_HELLO_ACK, {})
                elif opcode == MSG_HELLO_ACK and not self.spectator:
                    self.hello_acks_received.add(sender_pid)
                    if sender_pid in self.manifest:
                        self.send_unreliable(self.manifest[sender_pid], MSG_PING, {"sent_at_ms": int(time.time() * 1000)})
                elif opcode == MSG_PING and not self.spectator:
                    self.send_unreliable(addr, MSG_PONG, {"echo_sent_at_ms": payload.get("sent_at_ms", 0)})
                elif opcode == MSG_PONG:
                    self.last_pong[sender_pid] = time.time()
                    rtt = (time.time() * 1000) - payload.get("echo_sent_at_ms", time.time() * 1000)
                    self.channel_rtt[sender_pid] = rtt / 1000.0
                    self.channel_rto_base[sender_pid] = max(0.200, min(RTO_MAX, (rtt / 1000.0) * 2.5))
                    self.channel_rto[sender_pid] = self.channel_rto_base[sender_pid]
                elif opcode == MSG_SEED_COMMIT:
                    self._handle_seed_commit(sender_pid, payload)
                elif opcode == MSG_SEED_REVEAL:
                    self._handle_seed_reveal(sender_pid, payload)
                elif opcode == MSG_RING_CONFIRM:
                    self._handle_ring_confirm(sender_pid, payload)
                elif opcode == MSG_CARD_COMMIT:
                    self._handle_card_commit(sender_pid, payload)
                elif opcode == MSG_CARD_REVEAL:
                    self._handle_card_reveal(sender_pid, payload)
                elif opcode == MSG_ACTION_ANNOUNCE:
                    self._handle_action_announce(sender_pid, payload)
                elif opcode == MSG_HAND_PASS:
                    self._handle_hand_pass(sender_pid, payload)
                elif opcode == MSG_RESOURCE_QUERY and not self.spectator:
                    self._handle_resource_query(sender_pid, payload)
                elif opcode == MSG_RESOURCE_OFFER and not self.spectator:
                    self._handle_resource_offer(sender_pid, payload)
                elif opcode == MSG_RESOURCE_BUY and not self.spectator:
                    self._handle_resource_buy(sender_pid, payload)
                elif opcode == MSG_AGE_END:
                    self._handle_age_end(sender_pid, payload)
                elif opcode == MSG_SCORE_REPORT:
                    self._handle_score_report(sender_pid, payload)
                elif opcode == MSG_GAME_END:
                    print("\n[+] Consensus reached: GAME_END broadcast confirmed.")
                elif opcode == MSG_DIRECT_MESSAGE and not self.spectator:
                    print(f"\n[DM from Peer {sender_pid}]: {payload.get('text')}")
                elif opcode == MSG_GROUP_MESSAGE and not self.spectator:
                    print(f"\n[GROUP CHAT]: {payload.get('text')}")
                elif opcode == MSG_DISCONNECT:
                    self._handle_disconnect(sender_pid, payload)
                elif opcode == MSG_ERROR:
                    print(f"\n[!] ERROR BROADCAST: {payload.get('code')} -> {payload.get('detail')}")
                    self._handle_error(sender_pid, payload)

            except ConnectionResetError:
                continue
            except Exception as e:
                print(f"[!] _game_listener error: {type(e).__name__}: {e}")


def main():
    parser = argparse.ArgumentParser(description="7 Wonders Peer Node (RFC 7WD-1)")
    parser.add_argument("--name", required=True, help="Player or spectator name")
    parser.add_argument("--room", default="cs-demo", help="Room code for Lobby hash derivation")
    parser.add_argument("--port", type=int, required=True, help="Game UDP port")
    parser.add_argument("--host", default="127.0.0.1", help="IP to bind AND advertise to peers (use your LAN IP for multi-PC play)")
    parser.add_argument("--cards", default="Card Database 7WD.xlsx", help="Path to the card database spreadsheet")
    parser.add_argument("--lobby_port", type=int, default=7777, help="Lobby discovery port")
    parser.add_argument("--verbose", action="store_true", default=False, help="Enable verbose network logging")
    parser.add_argument("--spectator", action="store_true", help="Launch in Creative Extension Spectator Role (Bonus 10 pts)")
    parser.add_argument("--drop-to", default="", help="TEST ONLY: comma-separated manifest peer ids to silently drop all outgoing game packets to (simulates a dead link)")
    args = parser.parse_args()

    node = Peer7WDNode(
        display_name=args.name,
        room_code=args.room,
        host=args.host,
        game_port=args.port,
        lobby_port=args.lobby_port,
        verbose=args.verbose,
        spectator=args.spectator,
        card_db=args.cards,
        drop_to=[int(x) for x in args.drop_to.split(",") if x.strip()]
    )

    role_desc = "SPECTATOR MODE (Bonus Extension)" if args.spectator else "PLAYER NODE"
    print(f"=== 7WD Node Started: '{args.name}' | {role_desc} | Game Port: {args.port} | Room: '{args.room}' ===")

    print("\nCommands:")
    if not args.spectator:
        print("  start                    - Start Seed Commit ceremony")
        print("  pick <idx> [action]      - Draft card (action: BUILD, DISCARD, WONDER)")
        print("  trade <left/right> <res> - Query neighbor for resource")
        print("  dm <peer_id> <text>      - Send DIRECT_MESSAGE (0x18)")
        print("  msg <text>               - Send GROUP_MESSAGE (0x19)")
    else:
        print("  board                    - Display live spectator overview")
    print("  ping <peer_id>           - Ping peer to test RTT/RTO")
    print("  verbose                  - Toggle runtime verbose mode on/off")
    print("  roster                   - Show manifest, seating order and liveness")
    print("  drop <peer_id>           - toggle silently dropping our outgoing packets to a peer")
    print("  quit                     - Exit node\n")

    while node.running:
        try:
            line = input().strip()
            if not line:
                continue
            parts = line.split(" ", 2)
            cmd = parts[0].lower()

            if cmd == "start" and not node.spectator:
                node.start_seed_ceremony()
            elif cmd == "board" and node.spectator:
                node.print_spectator_dashboard()
            elif cmd == "pick" and not node.spectator and len(parts) > 1:
                action = parts[2].upper() if len(parts) > 2 else "BUILD"
                node.draft_action(int(parts[1]), action)
            elif cmd == "trade" and not node.spectator and len(parts) > 2:
                node.trade_resource(parts[1], parts[2])
            elif cmd == "dm" and not node.spectator and len(parts) > 2:
                node.send_reliable(int(parts[1]), MSG_DIRECT_MESSAGE, {"text": clip_text(parts[2])})
            elif cmd == "msg" and not node.spectator and len(parts) > 1:
                node.broadcast_mesh(MSG_GROUP_MESSAGE, {"text": clip_text(line.split(" ", 1)[1])})
            elif cmd == "ping" and len(parts) > 1:
                target_pid = int(parts[1])
                if target_pid in node.manifest:
                    node.send_unreliable(node.manifest[target_pid], MSG_PING, {"sent_at_ms": int(time.time() * 1000)})
            elif cmd == "verbose":
                node.verbose = not node.verbose
                print(f"[*] Verbose Logging: {'ENABLED' if node.verbose else 'DISABLED'}")
            elif cmd == "drop" and len(parts) > 1:
                dpid = int(parts[1])
                if dpid in node.drop_to_pids:
                    node.drop_to_pids.discard(dpid)
                    print(f"[*] No longer dropping outgoing packets to peer {dpid}")
                else:
                    node.drop_to_pids.add(dpid)
                    print(f"[*] TEST: silently dropping ALL outgoing packets to peer {dpid}")
            elif cmd == "roster":
                print(f"Manifest: {node.manifest_names}")
                print(f"Seating Ring: {node.seating_order} (My Seat: {node.my_seat})")
                print(f"Live: {node._live_pids()} | Disconnected: {sorted(node.disconnected_peers)} | Failed channels: {sorted(node.failed_channels)}")
            elif cmd == "quit":
                node.announce_exit("USER_QUIT")
                node.leave_lobby()
                node.running = False
                break
        except ValueError:
            print("[!] Invalid arguments: peer ids and card indexes must be numbers (use 'roster' to see peer ids).")
        except KeyboardInterrupt:
            node.announce_exit("USER_QUIT")
            node.leave_lobby()
            node.running = False
            break

if __name__ == "__main__":
    main()
