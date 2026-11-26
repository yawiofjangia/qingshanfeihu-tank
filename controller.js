// qingshanfeihu-tank v3.1 — original Armor controller for battle.training (rules s2.0.0).
//
// v3.1 = v3 (draft A apc+drone+mbt+scout + v2.2 fixes) + two fixes for the
// v2 H2H loss (13-27): (1) SQUAD PUSH — once O1 is secure, the MBT + scout
// push to O2 as a pair while the APC stays on O1 (v3 only sent the lone
// scout, which 2 APCs drove off while v2 banked 2x score on O2 all game);
// (2) HOLDER-APC CLAMP — an APC holding a point we own is never dragged
// off the capture radius by a kite or an engage chase (v3's APC drifted
// off O1 twice, dropping its score rate). The push MBT is exempt from
// the combat/mutual-support leashes while advancing on O2 (spearhead).
// Two more fixes after the first v3.1 gate run (H2H 20-20, exactly 50%):
// (3) o1Secure enemy radius 25 -> 15 — an enemy merely passing 24 tiles
// from O1 (en route elsewhere) blocked the push all game; the push fired
// at ~t=2400 instead of ~t=1200. (4) The late-game attack rule no longer
// yanks a unit off a point it is holding — it used to drag the APC off a
// held O1, losing the point and triggering the push recall (oscillation).
// v3 = draft A (apc+drone+mbt+scout, 11 pts) + the v2.2 fixes, on the v2.2
// codebase (controller-v2.js, DRAFT_MODE "C" -> "A"; everything else
// identical). Rationale: v2 (4x APC) won the house gauntlet locally
// (136-24-0 = 85.0%) but is only 21W-25L-10D (37.5%) live in the cup
// (2026-11-25 11:19 JST, 56 sets, rating 1137, rank 259/345) — it wins on
// score while taking heavy damage and cannot hurt an MBT from the front
// (10 dmg vs 20 front armor). Draft A was the best gauntlet draft in v2.0
// screening (148-12-0 = 92.5%) and brings a real MBT (front-armor duels,
// focus-fire damage), a drone (shared sightings — top live bots fire
// 50-61 shots vs our 7-12) and a scout (finishes isolated low-HP enemies,
// peels to the second objective once O1 is secure).
// v2.2 fixes carried over unchanged:
//   1. moveToPoint() routes off-post moves through a cached BFS field
//      centred on the goal tile (no more straight-line drives into the
//      river; the scout no longer freezes at a ford for 2800 ticks).
//   2. COMBAT LEASH — a ground unit with an enemy within 20 tiles and no
//      friendly ground unit within 12 falls back toward its nearest
//      friendly instead of fighting alone (unless already holding its
//      objective).
//   3. MUTUAL-SUPPORT LEASH (off-point only): regroup when >18 tiles from
//      every friendly ground unit, even with no enemy near.
// Gates (same as v2): gauntlet >= v2's 136-24-0 AND H2H vs v2 > 50% over
// 40 games, else do not upload. Note v2.0 mode A failed H2H vs v1 (9-11,
// mirror-inertness); mode A vs mode C is a different matchup (MBT+scout+
// drone vs 4 APCs), so the H2H gate is the real test here.
const FP = 65536, FULL = 4096, TAU = Math.PI * 2;

// Draft mode under test.
//   "A" apc+drone+mbt+scout (11 pts — submission candidate: best gauntlet)
//   "B" drone+drone+mbt+mbt (12 pts, 7-day meta best: 56.6% win rate)
//   "C" apc*4 | "D" apc+mbt+mbt
//   "E" adaptive (missile on 2-objective maps) — TESTED, REGRESSED
//       (gauntlet 131-29-0, H2H 7-12-1 vs v1); not the submission.
const DRAFT_MODE = "A";

const DRAFTS = {
  A: ["apc", "drone", "mbt", "scout"],
  B: ["drone", "drone", "mbt", "mbt"],
  C: ["apc", "apc", "apc", "apc"],
  D: ["apc", "mbt", "mbt"],
  E: null, // adaptive, see draft()
};

let R = null, MAP = null, SIDE = 0, W = 128, H = 128;
let SPAWN = [0, 0];
let OBJS = [];
let PASS = null;
let FIELDS = {};
let FIELDCACHE = new Map();   // "qx,qy" -> Int32Array BFS field to that goal
let MEM = new Map();
let UST = new Map();
let ASSIGN = new Map();       // unit id -> objective index (sticky)
let SECURE_TICKS = 0;
let PEEL_AT = -1;
let PUSH_AT = -1;   // v3.1: tick the squad push to O2 started, -1 = not pushing

function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }
function angTo(ax, ay, bx, by) {
  let a = Math.round(Math.atan2(by - ay, bx - ax) / TAU * FULL);
  return ((a % FULL) + FULL) % FULL;
}
function angDiff(a, b) { let d = (b - a) % FULL; if (d < 0) d += FULL; return d > FULL / 2 ? d - FULL : d; }
function inB(tx, ty) { return tx >= 0 && ty >= 0 && tx < W && ty < H; }
function tIdx(tx, ty) { return ty * W + tx; }
function passT(tx, ty) { return inB(tx, ty) && PASS[tIdx(tx, ty)] === 1; }
function distT(ax, ay, bx, by) { const dx = (bx - ax) / FP, dy = (by - ay) / FP; return Math.sqrt(dx * dx + dy * dy); }

function bfs(gx, gy) {
  const dist = new Int32Array(W * H).fill(-1);
  if (!passT(gx, gy)) return dist;
  const q = new Int32Array(W * H);
  let qh = 0, qt = 0;
  dist[tIdx(gx, gy)] = 0; q[qt++] = tIdx(gx, gy);
  while (qh < qt) {
    const c = q[qh++], cx = c % W, cy = (c / W) | 0, nd = dist[c] + 1;
    if (cx + 1 < W) { const n = c + 1; if (dist[n] < 0 && PASS[n]) { dist[n] = nd; q[qt++] = n; } }
    if (cx - 1 >= 0) { const n = c - 1; if (dist[n] < 0 && PASS[n]) { dist[n] = nd; q[qt++] = n; } }
    if (cy + 1 < H) { const n = c + W; if (dist[n] < 0 && PASS[n]) { dist[n] = nd; q[qt++] = n; } }
    if (cy - 1 >= 0) { const n = c - W; if (dist[n] < 0 && PASS[n]) { dist[n] = nd; q[qt++] = n; } }
  }
  return dist;
}

function pathFrom(field, fx, fy) {
  let tx = Math.floor(fx / FP), ty = Math.floor(fy / FP);
  if (!inB(tx, ty)) return [];
  const pts = [];
  let guard = 0;
  while (guard++ < 600) {
    const d = field[tIdx(tx, ty)];
    if (d < 0) break;
    pts.push([tx, ty]);
    if (d === 0) break;
    let best = null, bd = d;
    const nb = [[1, 0], [-1, 0], [0, 1], [0, -1]];
    for (let i = 0; i < 4; i++) {
      const nx = tx + nb[i][0], ny = ty + nb[i][1];
      if (!inB(nx, ny)) continue;
      const nd = field[tIdx(nx, ny)];
      if (nd >= 0 && nd < bd) { bd = nd; best = [nx, ny]; }
    }
    if (!best) break;
    tx = best[0]; ty = best[1];
  }
  const out = [];
  for (let i = 0; i < pts.length; i += 3) out.push([(pts[i][0] + 0.5) * FP, (pts[i][1] + 0.5) * FP]);
  const last = pts[pts.length - 1];
  if (last) {
    const lx = (last[0] + 0.5) * FP, ly = (last[1] + 0.5) * FP;
    if (!out.length || out[out.length - 1][0] !== lx || out[out.length - 1][1] !== ly) out.push([lx, ly]);
  }
  return out;
}

function getUST(u) {
  let st = UST.get(u.id);
  if (!st) { st = { path: null, pi: 0, pathKey: "", post: null, stuck: 0, boUntil: -1, boSteer: 0, lockId: 0 }; UST.set(u.id, st); }
  return st;
}

function steerTo(u, spec, gx, gy, order, slow) {
  const want = angTo(u.x, u.y, gx, gy);
  const d = angDiff(u.heading, want);
  order.steer = clamp(Math.round(d / spec.turnRate * FP), -FP, FP);
  order.throttle = Math.abs(d) > 512 ? Math.round(FP * 0.25) : (slow ? Math.round(FP * 0.5) : FP);
  return Math.abs(d) <= 256;
}

function steerDirect(u, spec, gx, gy, order) {
  if (spec.air) { steerTo(u, spec, gx, gy, order); return; }
  let want = angTo(u.x, u.y, gx, gy);
  const offs = [0, 341, -341, 683, -683, 1024, -1024, 1536, -1536];
  for (let i = 0; i < offs.length; i++) {
    const a = (want + offs[i]) & (FULL - 1);
    const rad = a / FULL * TAU;
    const px = u.x + Math.cos(rad) * FP * 1.5, py = u.y + Math.sin(rad) * FP * 1.5;
    if (passT(Math.floor(px / FP), Math.floor(py / FP))) { want = a; break; }
  }
  const d = angDiff(u.heading, want);
  order.steer = clamp(Math.round(d / spec.turnRate * FP), -FP, FP);
  order.throttle = Math.abs(d) > 512 ? Math.round(FP * 0.25) : FP;
}

// True if the straight line between two points crosses impassable terrain
// (sampled per tile). Used to skip the BFS when direct steering suffices.
function lineBlocked(ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay;
  const steps = Math.max(1, Math.ceil(Math.sqrt(dx * dx + dy * dy) / FP));
  for (let i = 1; i < steps; i++) {
    const x = ax + dx * i / steps, y = ay + dy * i / steps;
    if (!passT(Math.floor(x / FP), Math.floor(y / FP))) return true;
  }
  return false;
}

// Move a ground unit toward an arbitrary point, routed around the river by a
// BFS field centred on the (quantized) goal tile. Fields are cached so a
// moving goal only costs a recompute when it crosses a 2-tile block. When
// the straight line is clear, direct steering is used instead — a full BFS
// costs ~40 ms in Node (far more in the ladder's QuickJS) and would blow
// the per-tick budget, so it is only paid when the river is actually in
// the way.
function moveToPoint(u, spec, st, gx, gy, order) {
  if (spec.air) { steerDirect(u, spec, gx, gy, order); return true; }
  if (!lineBlocked(u.x, u.y, gx, gy)) { st.pathKey = ""; steerDirect(u, spec, gx, gy, order); return true; }
  const gtx = Math.floor(gx / FP), gty = Math.floor(gy / FP);
  const qx = gtx >> 1, qy = gty >> 1;
  const key = "p" + qx + "," + qy;
  let field = FIELDCACHE.get(key);
  if (!field) {
    field = bfs(gtx, gty);
    FIELDCACHE.set(key, field);
    if (FIELDCACHE.size > 8) {
      const first = FIELDCACHE.keys().next().value;
      FIELDCACHE.delete(first);
    }
  }
  const pkey = key + ":" + gtx + "," + gty;
  if (st.pathKey !== pkey || !st.path) {
    st.path = pathFrom(field, u.x, u.y);
    st.pi = 0; st.pathKey = pkey;
  }
  if (st.path && st.path.length && st.pi < st.path.length) {
    const wp = st.path[st.pi];
    const dx = wp[0] - u.x, dy = wp[1] - u.y;
    if (dx * dx + dy * dy < (0.7 * FP) * (0.7 * FP)) { st.pi++; return st.pi < st.path.length; }
    steerTo(u, spec, wp[0], wp[1], order);
    return true;
  }
  if (st.path && st.path.length) return false;
  steerDirect(u, spec, gx, gy, order);
  return true;
}

function moveUnit(u, spec, st, gx, gy, fieldKey, order) {
  if (spec.air) { steerDirect(u, spec, gx, gy, order); return true; }
  const gtx = Math.floor(gx / FP), gty = Math.floor(gy / FP);
  const key = (fieldKey || "direct") + ":" + gtx + "," + gty;
  if (fieldKey && FIELDS[fieldKey]) {
    if (st.pathKey !== key || !st.path) {
      st.path = pathFrom(FIELDS[fieldKey], u.x, u.y);
      st.pi = 0; st.pathKey = key;
    }
    if (st.path && st.path.length && st.pi < st.path.length) {
      const wp = st.path[st.pi];
      const dx = wp[0] - u.x, dy = wp[1] - u.y;
      if (dx * dx + dy * dy < (0.7 * FP) * (0.7 * FP)) { st.pi++; return st.pi < st.path.length; }
      steerTo(u, spec, wp[0], wp[1], order);
      return true;
    }
    if (st.path && st.path.length) return false;
    steerDirect(u, spec, gx, gy, order);
    return true;
  }
  steerDirect(u, spec, gx, gy, order);
  return true;
}

function objOrder() {
  return OBJS.map((ob, i) => i).sort((a, b) => {
    if (OBJS[a].weight !== OBJS[b].weight) return OBJS[b].weight - OBJS[a].weight;
    const da = distT(SPAWN[0], SPAWN[1], OBJS[a].x, OBJS[a].y);
    const db = distT(SPAWN[0], SPAWN[1], OBJS[b].x, OBJS[b].y);
    return da - db;
  });
}

function computePosts(o) {
  const perObj = {};
  for (const u of o.units) {
    if (!u.alive) continue;
    const oi = ASSIGN.get(u.id);
    if (oi === undefined) continue;
    (perObj[oi] = perObj[oi] || []).push(u);
  }
  for (const k of Object.keys(perObj)) {
    const us = perObj[k];
    const ob = OBJS[+k];
    const rad = Math.max(1, Math.min(3.5, ob.radius / FP - 1.5));
    let ring = 0;
    const nRing = Math.max(1, us.filter(x => x.kind !== "apc").length);
    us.forEach((u) => {
      const st = getUST(u);
      if (u.kind === "apc") { st.post = [ob.x, ob.y]; return; }
      const a = (ring++ / nRing) * TAU + 0.6;
      st.post = [ob.x + Math.cos(a) * rad * FP, ob.y + Math.sin(a) * rad * FP];
    });
  }
}

// v3.1: an APC holding a point we own must not be dragged off the capture
// radius by a kite or an engage chase (v3 lost O1 score twice this way in
// the v2 H2H). Clamp the destination to inside the radius, 1 tile margin.
function clampHold(oi, gx, gy) {
  const ob = OBJS[oi];
  if (!ob) return [gx, gy];
  const rad = ob.radius / FP;
  const d = distT(gx, gy, ob.x, ob.y);
  const maxR = Math.max(0.5, rad - 1);
  if (d <= maxR) return [gx, gy];
  const a = angTo(ob.x, ob.y, gx, gy) / FULL * TAU;
  return [ob.x + Math.cos(a) * maxR * FP, ob.y + Math.sin(a) * maxR * FP];
}
function isHolderAPC(u, oi, o) {
  return u.kind === "apc" && oi !== undefined && o.objectives && o.objectives[oi] && o.objectives[oi].owner === SIDE;
}

function assignInitial(o) {
  const order = objOrder();
  const o1 = order[0];
  ASSIGN.clear();
  const ground = o.units.filter(u => u.alive && !R.units[u.kind].air);
  if (DRAFT_MODE === "C") {
    ground.forEach((u, i) => ASSIGN.set(u.id, order[i % order.length]));
  } else {
    for (const u of ground) ASSIGN.set(u.id, o1);
  }
  computePosts(o);
}

function predict(c, ticks) {
  const rad = c.heading / FULL * TAU;
  return [c.x + Math.cos(rad) * c.speed * ticks, c.y + Math.sin(rad) * c.speed * ticks];
}

const FOCUS_PRI = { mbt: 100, missile: 90, apc: 70, artillery: 65, engineer: 50, scout: 40, drone: 25 };
function focusTarget(o) {
  let best = null, bs = -1;
  for (const c of o.contacts) {
    let dmin = Infinity;
    for (const u of o.units) {
      if (!u.alive) continue;
      const d = distT(u.x, u.y, c.x, c.y);
      if (d < dmin) dmin = d;
    }
    const frac = c.hpFrac / 65536;
    const s = (FOCUS_PRI[c.kind] || 20) * (2 - frac) / (1 + dmin / 25);
    if (s > bs) { bs = s; best = c; }
  }
  return best;
}

function targetFor(u, spec, o, focus) {
  const range = spec.gun && spec.gun.maxRange ? spec.gun.maxRange / FP : 0;
  if (focus && range > 0) {
    const d = distT(u.x, u.y, focus.x, focus.y);
    if (d <= range) return focus;
  }
  let best = null, bs = -1;
  for (const c of o.contacts) {
    const d = distT(u.x, u.y, c.x, c.y);
    if (range > 0 && d > range) continue;
    const frac = c.hpFrac / 65536;
    const pri = u.kind === "scout" ? { drone: 100, scout: 70, mbt: 40, apc: 40, missile: 50, artillery: 50, engineer: 40 }[c.kind] || 20
      : (FOCUS_PRI[c.kind] || 20);
    const s = pri * (2 - frac) / (1 + d / 25);
    if (s > bs) { bs = s; best = c; }
  }
  return best;
}

function fireControl(u, spec, tgt, o, order) {
  if (!tgt) return;
  const dt = distT(u.x, u.y, tgt.x, tgt.y);
  if (spec.gun.mode === "direct" && spec.gun.damage > 0) {
    if (dt > spec.gun.maxRange / FP || u.reload !== 0) return;
    const flight = Math.max(1, Math.round(dt / Math.max(0.01, spec.gun.shellSpeed / FP)));
    const p = predict(tgt, flight);
    const px = Math.round(p[0]), py = Math.round(p[1]);
    order.aimAt = [px, py];
    order.fire = [px, py];
  }
}

function missileFire(u, spec, o, order) {
  if (u.ammo === 0) return;
  const st = getUST(u);
  let lt = null;
  if (st.lockId) {
    for (const c of o.contacts) if (c.id === st.lockId) { lt = c; break; }
  }
  if (!lt) {
    let best = null, bs = -1;
    for (const c of o.contacts) {
      if (c.kind === "scout" || c.kind === "drone") continue;
      const d = distT(u.x, u.y, c.x, c.y);
      if (d < spec.gun.minRange / FP || d > spec.gun.maxRange / FP) continue;
      const s = (FOCUS_PRI[c.kind] || 20) * (2 - c.hpFrac / 65536) / (1 + d / 25);
      if (s > bs) { bs = s; best = c; }
    }
    if (best) { st.lockId = best.id; lt = best; } else { st.lockId = 0; return; }
  }
  const d = distT(u.x, u.y, lt.x, lt.y);
  if (d < spec.gun.minRange / FP || d > spec.gun.maxRange / FP) return;
  order.target = lt.id;
  const flight = Math.max(1, Math.round(d / Math.max(0.01, spec.gun.shellSpeed / FP)));
  const p = predict(lt, flight);
  order.aimAt = [Math.round(p[0]), Math.round(p[1])];
  if (u.lockTicks >= spec.gun.lockTicks && u.reload === 0 && u.ammo !== 0) order.fire = true;
}

globalThis.controller = {
  draft(h) {
    const d = h.draft;
    if (!d) return undefined;
    const nObj = (h.objectives || []).length;
    let pick;
    if (DRAFT_MODE === "E") pick = nObj >= 3 ? ["apc", "drone", "mbt", "scout"] : ["mbt", "missile", "drone", "scout"];
    else pick = DRAFTS[DRAFT_MODE] || DRAFTS.A;
    const cost = pick.reduce((c, k) => c + (d.costs[k] ?? 99), 0);
    if (cost <= d.budget && pick.every(k => d.roster.includes(k))) return pick;
    return undefined;
  },

  hello(h) {
    R = h.rules; MAP = h.map; SIDE = h.side; W = MAP.width; H = MAP.height;
    OBJS = (h.objectives || []).map(ob => ({ x: ob.x, y: ob.y, weight: ob.weight, radius: ob.radius }));
    const s = MAP.spawns[SIDE];
    SPAWN = [(s[0] + 0.5) * FP, (s[1] + 0.5) * FP];
    PASS = new Uint8Array(W * H);
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
      PASS[y * W + x] = (R.terrainSpeed[MAP.terrain[y * W + x]] > 0) ? 1 : 0;
    }
    FIELDS = {};
    OBJS.forEach((ob, i) => { FIELDS["o" + i] = bfs(Math.floor(ob.x / FP), Math.floor(ob.y / FP)); });
    FIELDS.spawn = bfs(Math.floor(SPAWN[0] / FP), Math.floor(SPAWN[1] / FP));
    FIELDCACHE = new Map();
    MEM.clear(); UST.clear(); ASSIGN.clear(); SECURE_TICKS = 0; PEEL_AT = -1; PUSH_AT = -1;
  },

  tick(o) {
    const orders = [];
    for (const c of o.contacts) MEM.set(c.id, { x: c.x, y: c.y, kind: c.kind, hp: c.hpFrac, tick: o.tick });
    for (const [id, m] of MEM) if (o.tick - m.tick > 400) MEM.delete(id);
    if (ASSIGN.size === 0) assignInitial(o);

    const order_idx = objOrder();
    const o1 = order_idx[0], o2 = order_idx.length > 1 ? order_idx[1] : order_idx[0];

    let o1Secure = false;
    if (o.objectives && o.objectives[o1] && o.objectives[o1].owner === SIDE && o.objectives[o1].state === "held") {
      o1Secure = true;
      for (const c of o.contacts) {
        // v3.1: 15 tiles, not 25 — an enemy merely passing 24 tiles away
        // (en route to another point) used to block the push all game.
        if (distT(c.x, c.y, OBJS[o1].x, OBJS[o1].y) < 15) { o1Secure = false; break; }
      }
    }
    SECURE_TICKS = o1Secure ? SECURE_TICKS + 1 : 0;

    const scout = o.units.find(u => u.alive && u.kind === "scout");
    const mbt = o.units.find(u => u.alive && u.kind === "mbt");
    if (scout && DRAFT_MODE !== "B" && DRAFT_MODE !== "D" && DRAFT_MODE !== "C") {
      const cur = ASSIGN.get(scout.id);
      if (cur === o1 && PEEL_AT < 0 && o.tick > 900 && SECURE_TICKS > 300) {
        let enemyNearO2 = false;
        for (const c of o.contacts) {
          if (distT(c.x, c.y, OBJS[o2].x, OBJS[o2].y) < 20) { enemyNearO2 = true; break; }
        }
        if (!enemyNearO2) { ASSIGN.set(scout.id, o2); PEEL_AT = o.tick; computePosts(o); }
      } else if (cur === o2) {
        // v3.1: in push mode the scout stays with the MBT on O2; the
        // combat leash (fall back toward the nearest friendly) handles
        // survival instead of a full retreat to O1.
        const inPush = PUSH_AT >= 0 && mbt && ASSIGN.get(mbt.id) === o2;
        if (!inPush) {
          let threat = false;
          for (const c of o.contacts) {
            if (distT(c.x, c.y, scout.x, scout.y) < 15) { threat = true; break; }
          }
          let friendNear = false;
          for (const u of o.units) {
            if (!u.alive || u.id === scout.id || R.units[u.kind].air) continue;
            if (distT(u.x, u.y, scout.x, scout.y) < 12) { friendNear = true; break; }
          }
          if (threat && !friendNear) { ASSIGN.set(scout.id, o1); PEEL_AT = -1; computePosts(o); }
        }
      }
    }

    // v3.1 SQUAD PUSH: once O1 is secure, the MBT + scout push to O2 as a
    // pair to contest/deny it, while the APC stays on O1 to keep the 2x
    // scoring rate. (v3 lost the v2 H2H because only the lone scout went
    // to O2 and was driven off by 2 APCs, while v2 banked 2x score there
    // all game. The MBT alone killed 2 of v2's APCs early — it just never
    // pushed onto O2 to convert the kills.) The push MBT is the spearhead:
    // it is exempt from the combat/mutual-support leashes while advancing.
    if (mbt && DRAFT_MODE !== "B" && DRAFT_MODE !== "D" && DRAFT_MODE !== "C") {
      if (PUSH_AT < 0) {
        const mbtOi = ASSIGN.get(mbt.id);
        const o2Owned = o.objectives && o.objectives[o2] && o.objectives[o2].owner === SIDE;
        if (mbtOi === o1 && o.tick > 900 && SECURE_TICKS > 300 && !o2Owned && mbt.hp > mbt.maxHp * 0.5) {
          ASSIGN.set(mbt.id, o2);
          if (scout && ASSIGN.get(scout.id) === o1) ASSIGN.set(scout.id, o2);
          PUSH_AT = o.tick;
          computePosts(o);
        }
      } else {
        // Recall: O1 lost — the MBT (and scout) go back to retake it.
        const o1Lost = !o.objectives || !o.objectives[o1] || o.objectives[o1].owner !== SIDE;
        if (o1Lost) {
          if (ASSIGN.get(mbt.id) === o2) ASSIGN.set(mbt.id, o1);
          if (scout && ASSIGN.get(scout.id) === o2) ASSIGN.set(scout.id, o1);
          PUSH_AT = -1;
          computePosts(o);
        }
      }
    }

    if (o.tick > 2900 && o.score && o.score[SIDE] < o.score[1 - SIDE]) {
      let attack = -1;
      for (const i of order_idx) {
        if (!o.objectives || o.objectives[i].owner !== SIDE) { attack = i; break; }
      }
      if (attack >= 0) {
        let changed = false;
        for (const u of o.units) {
          if (!u.alive || R.units[u.kind].air) continue;
          // v3.1: do not yank a unit off a point it is holding — the APC
          // is our only score-doubler; abandoning a held point to attack
          // loses the point (and the score race) for nothing, and the
          // loss then triggers the push recall, oscillating the squad.
          const cur = ASSIGN.get(u.id);
          if (cur !== undefined && o.objectives && o.objectives[cur] && o.objectives[cur].owner === SIDE
            && OBJS[cur] && distT(u.x, u.y, OBJS[cur].x, OBJS[cur].y) <= OBJS[cur].radius / FP) {
            continue;
          }
          if (cur !== attack) { ASSIGN.set(u.id, attack); changed = true; }
        }
        if (changed) computePosts(o);
      }
    }

    let huntTarget = null;
    if (scout) {
      for (const c of o.contacts) {
        if (c.hpFrac > 65536 * 0.3) continue;
        let isolated = true;
        for (const c2 of o.contacts) {
          if (c2.id === c.id) continue;
          if (distT(c2.x, c2.y, c.x, c.y) < 15) { isolated = false; break; }
        }
        if (!isolated) continue;
        if (distT(scout.x, scout.y, c.x, c.y) < 35) { huntTarget = c; break; }
      }
    }

    const focus = focusTarget(o);
    const aliveGround = o.units.filter(u => u.alive && !R.units[u.kind].air);

    for (const u of o.units) {
      if (!u.alive) continue;
      const spec = R.units[u.kind];
      const st = getUST(u);
      const order = { id: u.id };

      if (o.canMove) {
        let dodge = null;
        for (const inc of o.incoming || []) {
          if (distT(u.x, u.y, inc.x, inc.y) < 4.5 && inc.ticks < 45) { dodge = inc; break; }
        }
        if (dodge) {
          const a = angTo(dodge.x, dodge.y, u.x, u.y);
          steerDirect(u, spec, u.x + Math.cos(a / FULL * TAU) * 6 * FP, u.y + Math.sin(a / FULL * TAU) * 6 * FP, order);
        } else if (u.blocked) {
          st.stuck++;
          if (st.stuck > 2 && o.tick >= st.boUntil) {
            st.boUntil = o.tick + 14;
            st.boSteer = ((u.id + (o.tick >> 4)) & 1) ? FP : -FP;
            st.path = null; st.pathKey = "";
          }
          if (o.tick < st.boUntil) { order.throttle = -Math.round(FP * 0.7); order.steer = st.boSteer; }
          else { order.throttle = Math.round(FP * 0.5); order.steer = st.boSteer; }
        } else {
          st.stuck = 0;
          const oi = ASSIGN.get(u.id);
          const ob = oi !== undefined ? OBJS[oi] : null;

          if (u.kind === "drone") {
            const drones = o.units.filter(x => x.alive && x.kind === "drone");
            const idx = drones.findIndex(x => x.id === u.id);
            let anchorPt;
            if (DRAFT_MODE === "B" && idx === 1 && OBJS[o2]) anchorPt = [OBJS[o2].x, OBJS[o2].y];
            else if (ob) anchorPt = [ob.x, ob.y];
            else anchorPt = [(W / 2) * FP, (H / 2) * FP];
            let near = null, nd = Infinity;
            for (const c of o.contacts) { const d = distT(u.x, u.y, c.x, c.y); if (d < nd) { nd = d; near = c; } }
            if (near && nd < 25) {
              const a = angTo(near.x, near.y, u.x, u.y);
              steerDirect(u, spec, u.x + Math.cos(a / FULL * TAU) * 10 * FP, u.y + Math.sin(a / FULL * TAU) * 10 * FP, order);
            } else if (near && nd > 34) {
              steerDirect(u, spec, near.x, near.y, order);
            } else if (distT(u.x, u.y, anchorPt[0], anchorPt[1]) > 4) {
              steerDirect(u, spec, anchorPt[0], anchorPt[1], order);
            }
          } else if (u.kind === "scout" && huntTarget && u.id === scout.id) {
            moveToPoint(u, spec, st, huntTarget.x, huntTarget.y, order);
          } else if (u.kind === "missile") {
            if (spec.ammo !== undefined && u.ammo === 0 && o.tick < 3000) {
              if (distT(u.x, u.y, SPAWN[0], SPAWN[1]) < 2.5) { order.throttle = 0; order.steer = 0; }
              else moveUnit(u, spec, st, SPAWN[0], SPAWN[1], "spawn", order);
            } else {
              const lt = st.lockId ? MEM.get(st.lockId) : null;
              if (lt && o.tick - lt.tick < 40) {
                const d = distT(u.x, u.y, lt.x, lt.y);
                if (d < 9) {
                  const a = angTo(lt.x, lt.y, u.x, u.y);
                  moveToPoint(u, spec, st, u.x + Math.cos(a / FULL * TAU) * 6 * FP, u.y + Math.sin(a / FULL * TAU) * 6 * FP, order);
                } else if (d > 34) {
                  let noi = 0, nd = Infinity;
                  for (let i = 0; i < OBJS.length; i++) {
                    const dd = distT(lt.x, lt.y, OBJS[i].x, OBJS[i].y);
                    if (dd < nd) { nd = dd; noi = i; }
                  }
                  moveUnit(u, spec, st, OBJS[noi].x, OBJS[noi].y, "o" + noi, order);
                }
              } else if (st.post) {
                if (distT(u.x, u.y, st.post[0], st.post[1]) > 1.5)
                  moveUnit(u, spec, st, st.post[0], st.post[1], ob ? "o" + oi : null, order);
              }
            }
          } else {
            let moved = false;
            const range = spec.gun && spec.gun.maxRange ? spec.gun.maxRange / FP : 0;
            const postD = st.post ? distT(u.x, u.y, st.post[0], st.post[1]) : Infinity;

            // COMBAT LEASH: an enemy is close and no friendly ground unit
            // is near — do not fight alone (this is how the APC died at
            // the ford in the H2H loss). Fall back toward the nearest
            // friendly instead, unless already holding the objective.
            // v3.1: the push MBT is the spearhead — it does not fall back
            // from a fight with APCs while advancing on O2.
            const pushMbt = PUSH_AT >= 0 && u.kind === "mbt" && ASSIGN.get(u.id) === o2;
            const onPointCL = ob && distT(u.x, u.y, ob.x, ob.y) <= ob.radius / FP;
            if (!onPointCL && !pushMbt) {
              let enemyNearCL = false;
              for (const c of o.contacts) if (distT(c.x, c.y, u.x, u.y) < 20) { enemyNearCL = true; break; }
              let nearestCL = null, ndCL = Infinity;
              for (const f of aliveGround) {
                if (f.id === u.id) continue;
                const d = distT(u.x, u.y, f.x, f.y);
                if (d < ndCL) { ndCL = d; nearestCL = f; }
              }
              if (enemyNearCL && nearestCL && ndCL > 12) {
                moveToPoint(u, spec, st, nearestCL.x, nearestCL.y, order);
                moved = true;
              }
            }

            // APC kite: an enemy MBT/missile close in -> back toward the
            // nearest friendly MBT, staying near the objective.
            if (!moved && u.kind === "apc" && focus && (focus.kind === "mbt" || focus.kind === "missile")) {
              const fd = distT(u.x, u.y, focus.x, focus.y);
              if (fd < 9) {
                let guard = null, gd = Infinity;
                for (const f of aliveGround) {
                  if (f.kind !== "mbt") continue;
                  const d = distT(u.x, u.y, f.x, f.y);
                  if (d < gd) { gd = d; guard = f; }
                }
                if (guard) {
                  let gx = guard.x, gy = guard.y;
                  if (isHolderAPC(u, oi, o)) { const c = clampHold(oi, gx, gy); gx = c[0]; gy = c[1]; }
                  moveToPoint(u, spec, st, gx, gy, order);
                  moved = true;
                }
              }
            }

            // MUTUAL-SUPPORT LEASH (only while off the point, or opening):
            // no enemy near, but far from every friendly ground unit ->
            // regroup instead of fighting alone. Never abandons a held point.
            if (!moved) {
              const onPoint = ob && distT(u.x, u.y, ob.x, ob.y) <= ob.radius / FP;
              if (!onPoint && !pushMbt) {
                let enemyNear = false;
                for (const c of o.contacts) if (distT(c.x, c.y, u.x, u.y) < 20) { enemyNear = true; break; }
                let nearest = null, nd = Infinity;
                for (const f of aliveGround) {
                  if (f.id === u.id) continue;
                  const d = distT(u.x, u.y, f.x, f.y);
                  if (d < nd) { nd = d; nearest = f; }
                }
                if (!enemyNear && nearest && nd > 18) {
                  moveToPoint(u, spec, st, nearest.x, nearest.y, order);
                  moved = true;
                }
              }
            }

            // low-HP MBT swap: fall back behind a healthier sister MBT.
            if (!moved && u.kind === "mbt" && u.hp < u.maxHp * 0.4 && focus) {
              let sister = null;
              for (const f of aliveGround) {
                if (f.kind !== "mbt" || f.id === u.id) continue;
                if (f.hp > f.maxHp * 0.6 && distT(u.x, u.y, f.x, f.y) < 15) { sister = f; break; }
              }
              if (sister) {
                const a = angTo(focus.x, focus.y, sister.x, sister.y);
                moveToPoint(u, spec, st, sister.x + Math.cos(a / FULL * TAU) * 6 * FP, sister.y + Math.sin(a / FULL * TAU) * 6 * FP, order);
                moved = true;
              }
            }

            if (!moved) {
              let engage = null;
              if (focus && range > 0) {
                const d = distT(u.x, u.y, focus.x, focus.y);
                const contesting = ob && distT(focus.x, focus.y, ob.x, ob.y) <= ob.radius / FP + 3;
                if ((d <= range + 6 && d > range) || contesting) engage = focus;
              }
              if (engage) {
                if (postD < 10) {
                  let gx = engage.x, gy = engage.y;
                  if (isHolderAPC(u, oi, o)) { const c = clampHold(oi, gx, gy); gx = c[0]; gy = c[1]; }
                  moveToPoint(u, spec, st, gx, gy, order);
                } else if (st.post) {
                  moveUnit(u, spec, st, st.post[0], st.post[1], ob ? "o" + oi : null, order);
                }
              } else if (st.post && postD > 1.5) {
                moveUnit(u, spec, st, st.post[0], st.post[1], ob ? "o" + oi : null, order);
              }
            }
          }
        }
      }

      if (spec.gun && spec.gun.lockTicks) missileFire(u, spec, o, order);
      else if (spec.gun && spec.gun.mode === "direct" && spec.gun.damage > 0) {
        const tgt = targetFor(u, spec, o, focus);
        fireControl(u, spec, tgt, o, order);
      }
      orders.push(order);
    }
    return { units: orders };
  },
};
