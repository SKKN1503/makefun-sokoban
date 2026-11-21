import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const input = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const output = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const letters = 'udlr';

function solve(text) {
  const rows = text.replace(/\r/g, '').split('\n');
  while (rows.length && rows[rows.length - 1] === '') rows.pop();
  const w = Math.max(...rows.map(r => r.length)) + 2, h = rows.length + 2, n = w * h;
  const floor = new Uint8Array(n), goals = new Uint8Array(n), initial = new Set();
  let start = -1;
  for (let y = 0; y < rows.length; y++) for (let x = 0; x < rows[y].length; x++) {
    const c = rows[y][x], p = (y + 1) * w + x + 1;
    if (' .$*@+'.includes(c)) floor[p] = 1;
    if ('.*+'.includes(c)) goals[p] = 1;
    if ('$*'.includes(c)) initial.add(p);
    if ('@+'.includes(c)) start = p;
  }
  if (start < 0) return '';
  const ds = [-w, w, -1, 1];
  function walk(pos, boxes, allowed, target = -1) {
    const seen = new Int32Array(n); seen.fill(-1); seen[pos] = pos;
    const queue = [pos];
    for (let i = 0; i < queue.length; i++) {
      const p = queue[i];
      for (let d = 0; d < 4; d++) {
        const q = p + ds[d];
        if (allowed[q] && !boxes.has(q) && seen[q] < 0) { seen[q] = p * 4 + d; queue.push(q); }
      }
    }
    if (target < 0) return { seen, min: Math.min(...queue) };
    if (seen[target] < 0) return null;
    let path = '', p = target;
    while (p !== pos) { const v = seen[p], d = v % 4; path += letters[d]; p = (v - d) / 4; }
    return path.split('').reverse().join('');
  }
  function search(allowed, boxes0, pos, cap) {
    const goalList = []; for (let p = 0; p < n; p++) if (allowed[p] && goals[p]) goalList.push(p);
    if (goalList.length !== boxes0.length) return null;
    // Reverse pulls give both static dead squares and lower bounds for each goal.
    const dist = goalList.map(g => {
      const a = new Int16Array(n); a.fill(-1); a[g] = 0; const q = [g];
      for (let i = 0; i < q.length; i++) for (const d of ds) {
        const prev = q[i] - d, stand = prev - d;
        if (allowed[prev] && allowed[stand] && a[prev] < 0) { a[prev] = a[q[i]] + 1; q.push(prev); }
      }
      return a;
    });
    const cache = new Map();
    function heuristic(boxes) {
      const key = boxes.join(','); if (cache.has(key)) return cache.get(key);
      let dp = new Int32Array(1 << boxes.length); dp.fill(100000); dp[0] = 0;
      for (let mask = 0; mask < dp.length; mask++) {
        let k = 0; for (let v = mask; v; v &= v - 1) k++;
        if (k === boxes.length || dp[mask] === 100000) continue;
        for (let j = 0; j < boxes.length; j++) if (!(mask & (1 << j)) && dist[j][boxes[k]] >= 0) {
          const next = mask | (1 << j), value = dp[mask] + dist[j][boxes[k]];
          if (value < dp[next]) dp[next] = value;
        }
      }
      const value = dp[dp.length - 1]; cache.set(key, value); return value;
    }
    const heap = [];
    function less(a, b) { return a.f < b.f || (a.f === b.f && (a.h < b.h || (a.h === b.h && a.seq < b.seq))); }
    function put(a) { let i = heap.length; heap.push(a); while (i) { const j = (i - 1) >> 1; if (!less(a, heap[j])) break; heap[i] = heap[j]; i = j; } heap[i] = a; }
    function pop() { const result = heap[0], a = heap.pop(); if (heap.length) { let i = 0; while (true) { let j = i * 2 + 1; if (j >= heap.length) break; if (j + 1 < heap.length && less(heap[j + 1], heap[j])) j++; if (!less(heap[j], a)) break; heap[i] = heap[j]; i = j; } heap[i] = a; } return result; }
    const boxes = [...boxes0].sort((a,b) => a-b), firstH = heuristic(boxes);
    const reach = walk(pos, new Set(boxes), allowed), best = new Map();
    let seq = 0;
    const key = boxes.join(',') + ':' + reach.min;
    best.set(key, 0); put({ boxes, pos, g: 0, h: firstH, f: firstH, key, parent: null, seq: seq++ });
    let expanded = 0;
    while (heap.length && expanded++ < cap) {
      const cur = pop(); if (best.get(cur.key) !== cur.g) continue;
      if (cur.h === 0) {
        const pushes = []; for (let s = cur; s.parent; s = s.parent) pushes.push([s.box, s.dir]);
        pushes.reverse(); return pushes;
      }
      const occupied = new Set(cur.boxes), reachable = walk(cur.pos, occupied, allowed).seen;
      for (const box of cur.boxes) for (let dir = 0; dir < 4; dir++) {
        const delta = ds[dir], to = box + delta, behind = box - delta;
        if (!allowed[to] || occupied.has(to) || reachable[behind] < 0) continue;
        const next = cur.boxes.map(b => b === box ? to : b).sort((a,b) => a-b);
        const hh = heuristic(next); if (hh >= 100000) continue;
        const rr = walk(box, new Set(next), allowed), k = next.join(',') + ':' + rr.min, g = cur.g + 1;
        if (best.has(k) && best.get(k) <= g) continue;
        best.set(k, g); put({ boxes: next, pos: box, g, h: hh, f: g + hh, key: k, parent: cur, box, dir, seq: seq++ });
      }
    }
    return null;
  }
  // The player's horizontal floor run is the hallway. Removing it separates the rooms;
  // each component must connect through exactly one hallway articulation cell.
  const hall = new Uint8Array(n); hall[start] = 1;
  for (const d of [-1, 1]) for (let p = start + d; floor[p]; p += d) hall[p] = 1;
  const visited = new Uint8Array(n), rooms = [];
  let valid = true;
  for (let p = 0; p < n; p++) if (floor[p] && !hall[p] && !visited[p]) {
    const q = [p], doors = new Set(), boxes = []; let goalCount = 0; visited[p] = 1;
    for (let i = 0; i < q.length; i++) {
      const v = q[i]; if (initial.has(v)) boxes.push(v); if (goals[v]) goalCount++;
      for (const d of ds) { const t = v + d; if (hall[t]) doors.add(t); else if (floor[t] && !visited[t]) { visited[t] = 1; q.push(t); } }
    }
    if (!boxes.length && !goalCount) continue;
    if (doors.size !== 1 || boxes.length !== goalCount) { valid = false; break; }
    const door = [...doors][0], allowed = new Uint8Array(n); allowed[door] = 1; for (const v of q) allowed[v] = 1;
    rooms.push({ door, allowed, boxes });
  }
  if ([...initial].some(p => hall[p]) || rooms.reduce((a,r) => a + r.boxes.length, 0) !== initial.size) valid = false;
  let moves = '', player = start, boxes = new Set(initial), totalPushes = 0;
  function applyPushes(pushes, allowed) {
    for (const [box, dir] of pushes) {
      const path = walk(player, boxes, allowed, box - ds[dir]); if (path === null) return false;
      moves += path + letters[dir]; boxes.delete(box); boxes.add(box + ds[dir]); player = box; totalPushes++;
    }
    return true;
  }
  if (valid && rooms.length) {
    for (const room of rooms) {
      const path = walk(player, boxes, floor, room.door); if (path === null) { valid = false; break; }
      moves += path; player = room.door;
      const pushes = search(room.allowed, room.boxes, player, 2000000);
      if (!pushes || !applyPushes(pushes, room.allowed)) { valid = false; break; }
      const out = walk(player, boxes, room.allowed, room.door); if (out === null) { valid = false; break; }
      moves += out; player = room.door;
    }
  } else valid = false;
  if (!valid) {
    moves = ''; player = start; boxes = new Set(initial); totalPushes = 0;
    const pushes = search(floor, [...boxes], player, 150000);
    if (!pushes || !applyPushes(pushes, floor)) return '';
  }
  // Independently replay and verify the move count and solved position.
  let p = start, count = 0; const replay = new Set(initial);
  for (const c of moves) {
    const d = ds[letters.indexOf(c)], q = p + d;
    if (!floor[q]) return '';
    if (replay.has(q)) { if (!floor[q+d] || replay.has(q+d)) return ''; replay.delete(q); replay.add(q+d); count++; }
    p = q;
  }
  if (count !== totalPushes || [...replay].some(b => !goals[b]) || moves.length > 65535) return '';
  return moves;
}
for (const id of readdirSync(input).sort()) {
  let result = '';
  try { result = solve(readFileSync(join(input, id, 'level.txt'), 'utf8')); } catch {}
  mkdirSync(join(output, id), { recursive: true });
  writeFileSync(join(output, id, 'solution.txt'), result + '\n');
}
