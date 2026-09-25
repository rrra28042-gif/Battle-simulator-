'use strict';

// ═══════════════════════════════════════════════════════════════════════════════
//  CANVAS SETUP
// ═══════════════════════════════════════════════════════════════════════════════
const canvas = document.getElementById('canvas');
const ctx    = canvas.getContext('2d');

function resize() { canvas.width = window.innerWidth; canvas.height = window.innerHeight; }
resize();

// ═══════════════════════════════════════════════════════════════════════════════
//  CONSTANTS & SYMMETRIC STATS
// ═══════════════════════════════════════════════════════════════════════════════
const ATTACK_RANGE     = 5;
const ENGAGE_RADIUS    = 50;
const COMBAT_DETECT_PX = 30;
const COMBAT_UNLOCK_PX = 150;
const ATTACK_INTERVAL  = 30;   // 30 frames @ 60fps = 0.5s attack speed
const BASE_ATTACK      = 10;
const BASE_HP          = 100;
const BASE_SPEED       = 1.5;  // Symmetric unit & legion movement speed
const FRM_PAD          = 22;
const CPU_INTERVAL     = 60;   // frames ≈ 1 s between AI decisions

// Explicit Team Enum
const TEAM = {
    BLUE: 'blue',
    RED:  'red'
};

// ═══════════════════════════════════════════════════════════════════════════════
//  GLOBAL STATE
// ═══════════════════════════════════════════════════════════════════════════════
let legions       = [];
let allBoids      = [];
let fallen        = [];
let isDragging    = false;
let draggedLegion = null;
let dragOffset    = { x: 0, y: 0 };
let commandPulse  = null;
let victoryBanner = null;

// PvE globals
let gameMode    = 'PVP';  // 'PVP' | 'PVE'
let simSpeed    = 1;
let cpuTick     = 0;
let cpuActivity = null;

// ═══════════════════════════════════════════════════════════════════════════════
//  LEGION CLASS
// ═══════════════════════════════════════════════════════════════════════════════
class Legion {
    constructor(id, name, x, y, w, h, color, team, initialCount = 50) {
        this.id           = id;
        this.name         = name;
        this.x            = x;   this.y      = y;
        this.width        = w;   this.height = h;
        this.color        = color;
        this.team         = team; // 'blue' or 'red'
        this.units        = [];
        this.initialCount = initialCount;
        this.targetX      = x + w / 2;
        this.targetY      = y + h / 2;
        this.isSelected   = false;
        this.speed        = BASE_SPEED;
        this.state        = 'MARCH';
        this.formation    = 'SWARM';
        this.slots        = [];
    }

    get center() { return { x: this.x + this.width / 2, y: this.y + this.height / 2 }; }

    containsPoint(px, py) {
        return px >= this.x && px <= this.x + this.width &&
               py >= this.y && py <= this.y + this.height;
    }

    overlaps(o) {
        return !(this.x + this.width  < o.x || o.x + o.width  < this.x ||
                 this.y + this.height < o.y || o.y + o.height < this.y);
    }

    // ── Formation slot generation ──────────────────────────────────────────────
    getFormationSlots(count, enemyCenter) {
        if (count === 0) return [];

        const cx = this.x + this.width  / 2;
        const cy = this.y + this.height / 2;
        const fw = this.width  - FRM_PAD * 2;
        const fh = this.height - FRM_PAD * 2;

        let ex = 1, ey = 0;
        if (enemyCenter) {
            const edx = enemyCenter.x - cx, edy = enemyCenter.y - cy;
            const em  = Math.hypot(edx, edy);
            if (em > 0) { ex = edx / em; ey = edy / em; }
        } else {
            const edx = this.targetX - cx, edy = this.targetY - cy;
            const em  = Math.hypot(edx, edy);
            if (em > 0) { ex = edx / em; ey = edy / em; }
        }
        const px = -ey, py = ex;
        const slots = [];

        if (this.formation === 'LINE') {
            const frontN  = Math.ceil(count / 2);
            const rearN   = count - frontN;
            const rowSpan = Math.min(fw, fh) * 0.30;

            for (let c = 0; c < frontN; c++) {
                const spread = frontN > 1 ? (c / (frontN - 1) - 0.5) * fw : 0;
                slots.push({ dx: px * spread + ex * ( rowSpan/2), dy: py * spread + ey * ( rowSpan/2), rank: 0 });
            }
            for (let c = 0; c < rearN; c++) {
                const spread = rearN > 1 ? (c / (rearN - 1) - 0.5) * fw : 0;
                slots.push({ dx: px * spread + ex * (-rowSpan/2), dy: py * spread + ey * (-rowSpan/2), rank: 1 });
            }
            return slots;
        }

        if (this.formation === 'GRID') {
            const cols    = Math.ceil(Math.sqrt(count));
            const rows    = Math.ceil(count / cols);
            const side    = Math.min(fw, fh);
            const colStep = cols > 1 ? side / (cols - 1) : 0;
            const rowStep = rows > 1 ? side / (rows - 1) : 0;

            for (let r = 0; r < rows; r++) {
                for (let c = 0; c < cols; c++) {
                    if (slots.length >= count) break;
                    const depth  = rows > 1 ? ((rows-1)*0.5 - r) * rowStep : 0;
                    const spread = cols > 1 ? (c - (cols-1)*0.5) * colStep  : 0;
                    slots.push({ dx: px * spread + ex * depth, dy: py * spread + ey * depth, rank: r });
                }
            }
            return slots;
        }

        return [];
    }

    // ── Greedy nearest-slot assignment ─────────────────────────────────────────
    assignSlots(enemyCenter) {
        if (this.formation === 'SWARM') {
            this.slots = [];
            this.units.forEach(b => { b.slotIndex = -1; b.rank = 0; });
            return;
        }
        const count = this.units.length;
        if (count === 0) return;

        this.slots = this.getFormationSlots(count, enemyCenter);
        const cx   = this.x + this.width / 2, cy = this.y + this.height / 2;
        const slotOrder = [...this.slots.keys()].sort((a,b) => this.slots[a].rank - this.slots[b].rank);
        const used = new Set();

        for (const si of slotOrder) {
            const { dx, dy } = this.slots[si];
            const wx = cx + dx, wy = cy + dy;
            let bestIdx = -1, bestDist = Infinity;
            for (let ui = 0; ui < count; ui++) {
                if (used.has(ui)) continue;
                const d = Math.hypot(this.units[ui].position.x - wx, this.units[ui].position.y - wy);
                if (d < bestDist) { bestDist = d; bestIdx = ui; }
            }
            if (bestIdx >= 0) {
                used.add(bestIdx);
                this.units[bestIdx].slotIndex = si;
                this.units[bestIdx].rank      = this.slots[si].rank;
            }
        }
    }

    update(enemyLegion) {
        // Clean array cleanup at the start of every update frame
        const beforeCount = this.units.length;
        this.units = this.units.filter(u => {
            if ((u.hp <= 0 || u.isDead) && !u.wasCleanedUp) {
                u.isDead = true;
                u.wasCleanedUp = true;
                spawnFallen(u.position.x, u.position.y);
                return false;
            }
            return (u.hp > 0 && !u.isDead);
        });

        // Dynamic Formation Compact: If a unit dies, immediately re-run slot assignment
        if (this.units.length !== beforeCount) {
            if (this.formation !== 'SWARM') {
                this.assignSlots(enemyLegion ? enemyLegion.center : null);
            }
        }

        if (this.state !== 'MARCH') return;
        const cx = this.x + this.width/2, cy = this.y + this.height/2;
        const dx = this.targetX - cx,     dy = this.targetY - cy;
        const d  = Math.hypot(dx, dy);
        if (d > 1) { const mv = Math.min(this.speed, d); this.x += (dx/d)*mv; this.y += (dy/d)*mv; }
    }

    draw() {
        const cx = this.x + this.width / 2, cy = this.y + this.height / 2;
        const isCPU = gameMode === 'PVE' && this.team === TEAM.RED;

        // Background
        ctx.save();
        const bgAlpha = this.state === 'COMBAT' ? 0.18 : 0.09;
        ctx.fillStyle = this.team === TEAM.BLUE
            ? `rgba(59,130,246,${bgAlpha})`
            : `rgba(239,68,68,${bgAlpha})`;
        ctx.fillRect(this.x, this.y, this.width, this.height);

        // Border
        ctx.lineWidth   = this.isSelected ? 2.5 : 1.5;
        ctx.strokeStyle = this.color;
        ctx.setLineDash(this.isSelected       ? [8,4]
                      : this.state==='COMBAT' ? [3,3]
                      : []);
        if (this.isSelected) { ctx.shadowBlur = 14; ctx.shadowColor = this.color; }
        ctx.strokeRect(this.x, this.y, this.width, this.height);
        ctx.restore();

        // Dynamic Numerical Representation Text Label (positioned centered slightly above top edge: legion.y - 10)
        ctx.save();
        const activeCount = this.units.length;
        const isDefeated  = activeCount === 0;
        const labelText   = isDefeated ? 'DEFEATED' : `${this.name}: ${activeCount}/${this.initialCount}`;

        ctx.font         = 'bold 13px system-ui, -apple-system, sans-serif';
        ctx.textAlign    = 'center';
        ctx.textBaseline = 'middle';

        const labelX = cx;
        const labelY = this.y - 10;

        const metrics = ctx.measureText(labelText);
        const padX = 10;
        const boxW = metrics.width + padX * 2;
        const boxH = 20;
        const boxX = labelX - boxW / 2;
        const boxY = labelY - boxH / 2;

        // Semi-transparent dark background box behind text label
        ctx.fillStyle = 'rgba(15, 23, 42, 0.88)';
        ctx.beginPath();
        if (ctx.roundRect) {
            ctx.roundRect(boxX, boxY, boxW, boxH, 4);
        } else {
            ctx.rect(boxX, boxY, boxW, boxH);
        }
        ctx.fill();

        ctx.strokeStyle = isDefeated ? 'rgba(239, 68, 68, 0.7)' : (this.isSelected ? this.color : 'rgba(255, 255, 255, 0.18)');
        ctx.lineWidth   = 1;
        ctx.stroke();

        // Stroke text for maximum contrast over canvas clutter
        ctx.strokeStyle = '#020617';
        ctx.lineWidth   = 3;
        ctx.strokeText(labelText, labelX, labelY);

        // Fill text: bold, red if DEFEATED, vibrant team color if active
        if (isDefeated) {
            ctx.fillStyle = '#ef4444';
        } else {
            ctx.fillStyle = this.team === TEAM.BLUE ? '#93c5fd' : '#fca5a5';
        }
        ctx.fillText(labelText, labelX, labelY);
        ctx.restore();

        // Labels inside rectangle
        ctx.save();
        ctx.font      = '500 10px system-ui,sans-serif';
        ctx.fillStyle = this.state === 'COMBAT' ? '#fbbf24' : '#64748b';
        ctx.fillText(this.state === 'COMBAT' ? '⚔ COMBAT' : '➤ MARCH', this.x + 9, this.y + 18);

        // CPU indicator
        if (isCPU) {
            ctx.font      = '600 10px system-ui,sans-serif';
            ctx.fillStyle = '#fbbf24';
            ctx.fillText('🤖 CPU', this.x + 9, this.y + 32);
        }

        const fLabel = `[${this.formation}]`;
        ctx.font      = '500 10px system-ui,sans-serif';
        ctx.fillStyle = isCPU ? '#78350f' : '#334155';
        ctx.fillText(fLabel, this.x + this.width - ctx.measureText(fLabel).width - 8, this.y + 18);
        ctx.restore();

        // Formation slot dots when selected
        if (this.isSelected && this.formation !== 'SWARM' && this.slots.length > 0) {
            for (const s of this.slots) {
                ctx.beginPath();
                ctx.arc(cx + s.dx, cy + s.dy, 2.2, 0, Math.PI*2);
                ctx.fillStyle = s.rank === 0 ? 'rgba(255,255,255,0.30)' : 'rgba(255,255,255,0.12)';
                ctx.fill();
            }
        }

        // March target line
        if (this.state === 'MARCH') {
            const dtx = Math.hypot(this.targetX - cx, this.targetY - cy);
            if (dtx > 8) {
                ctx.save();
                ctx.beginPath();
                ctx.moveTo(cx, cy);
                ctx.lineTo(this.targetX, this.targetY);
                ctx.strokeStyle = this.team === TEAM.BLUE ? 'rgba(59,130,246,0.40)' : 'rgba(239,68,68,0.40)';
                ctx.lineWidth   = isCPU ? 1 : 1.5;
                ctx.setLineDash(isCPU ? [2,4] : [4,4]);
                ctx.stroke();
                ctx.beginPath();
                ctx.arc(this.targetX, this.targetY, isCPU ? 3 : 4, 0, Math.PI*2);
                ctx.fillStyle = this.color;
                ctx.fill();
                ctx.restore();
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  BOID CLASS (SYMMETRIC COMBAT & STATS)
// ═══════════════════════════════════════════════════════════════════════════════
class Boid {
    constructor(x, y, legion) {
        this.position       = { x, y };
        this.velocity       = { x: (Math.random()-0.5)*2, y: (Math.random()-0.5)*2 };
        this.legion         = legion;
        this.team           = legion.team; // TEAM.BLUE or TEAM.RED
        this.color          = legion.color;
        this.maxSpeed       = BASE_SPEED;
        this.maxForce       = 0.08;
        this.size           = 4.5;
        this.hp             = BASE_HP;
        this.attackPower    = BASE_ATTACK;
        this.attackCooldown = 0;
        this.isDead         = false;
        this.wasCleanedUp   = false;
        this.hitFlash       = 0;
        this.combatTarget   = null;
        this.slotIndex      = -1;
        this.rank           = 0;
    }

    findNearestEnemy(enemyLegion) {
        if (!enemyLegion || !enemyLegion.units.length) return { enemy: null, dist: Infinity };
        let nearest = null, nearDist = Infinity;
        for (const e of enemyLegion.units) {
            if (e.isDead || e.hp <= 0) continue;
            const d = Math.hypot(this.position.x - e.position.x, this.position.y - e.position.y);
            if (d < nearDist) { nearDist = d; nearest = e; }
        }
        return { enemy: nearest, dist: nearDist };
    }

    takeDamage(amount, attacker) {
        if (this.isDead || this.hp <= 0) return;
        this.hp -= amount;
        console.log(`${attacker.team.toUpperCase()} dealt ${amount} damage to ${this.team.toUpperCase()}. Target HP remaining: ${Math.max(0, this.hp)}`);
        this.hitFlash = 6;
        if (this.hp <= 0) {
            this.hp = 0;
            this.isDead = true;
        }
    }

    tick(enemyLegion) {
        if (this.isDead || this.hp <= 0) return;
        if (this.attackCooldown > 0) this.attackCooldown--;

        const inFormation = this.legion.formation !== 'SWARM';

        if (this.legion.state === 'COMBAT') {
            if (inFormation && this.rank > 0) {
                const { dist } = this.findNearestEnemy(enemyLegion);
                if (dist <= ENGAGE_RADIUS) {
                    this.combatBehaviour(enemyLegion);
                } else {
                    this.formationBehaviour();
                }
            } else {
                this.combatBehaviour(enemyLegion);
            }
        } else {
            inFormation ? this.formationBehaviour() : this.swarmBehaviour();
        }

        this.position.x += this.velocity.x;
        this.position.y += this.velocity.y;
    }

    // ── SWARM (Boids) ──────────────────────────────────────────────────────────
    swarmBehaviour() {
        const sep    = this.separate(allBoids, 20);
        const ali    = this.align();
        const coh    = this.cohere();
        const bounds = this.keepInBounds();
        this.velocity.x += sep.x*1.8 + ali.x + coh.x*1.2 + bounds.x*3;
        this.velocity.y += sep.y*1.8 + ali.y + coh.y*1.2 + bounds.y*3;
        this.clampSpeed();
    }

    cohere() { return this.seek(this.legion.center); }

    keepInBounds() {
        const pad = 12;
        const minX=this.legion.x+pad, maxX=this.legion.x+this.legion.width-pad;
        const minY=this.legion.y+pad, maxY=this.legion.y+this.legion.height-pad;
        let s = {x:0, y:0};
        if      (this.position.x < minX) s.x =  this.maxSpeed;
        else if (this.position.x > maxX) s.x = -this.maxSpeed;
        if      (this.position.y < minY) s.y =  this.maxSpeed;
        else if (this.position.y > maxY) s.y = -this.maxSpeed;
        if (s.x || s.y) {
            const m = Math.hypot(s.x, s.y);
            s.x = (s.x/m)*this.maxSpeed - this.velocity.x;
            s.y = (s.y/m)*this.maxSpeed - this.velocity.y;
            return this.limitForce(s);
        }
        return {x:0, y:0};
    }

    separate(boids, dist) {
        let s = {x:0, y:0}, c = 0;
        for (const o of boids) {
            if (o === this || o.isDead || o.hp <= 0) continue;
            const d = Math.hypot(this.position.x-o.position.x, this.position.y-o.position.y);
            if (d > 0 && d < dist) { s.x += (this.position.x-o.position.x)/d; s.y += (this.position.y-o.position.y)/d; c++; }
        }
        if (c > 0) {
            s.x /= c; s.y /= c;
            const m = Math.hypot(s.x, s.y);
            if (m > 0) { s.x = (s.x/m)*this.maxSpeed - this.velocity.x; s.y = (s.y/m)*this.maxSpeed - this.velocity.y; }
            return this.limitForce(s);
        }
        return {x:0, y:0};
    }

    align() {
        const nd = 40; let sum={x:0,y:0}, c=0;
        for (const o of this.legion.units) {
            if (o===this||o.isDead||o.hp<=0) continue;
            const d = Math.hypot(this.position.x-o.position.x, this.position.y-o.position.y);
            if (d>0 && d<nd) { sum.x+=o.velocity.x; sum.y+=o.velocity.y; c++; }
        }
        if (c > 0) {
            sum.x/=c; sum.y/=c;
            const m=Math.hypot(sum.x,sum.y);
            if (m>0) { sum.x=(sum.x/m)*this.maxSpeed; sum.y=(sum.y/m)*this.maxSpeed; }
            return this.limitForce({x:sum.x-this.velocity.x, y:sum.y-this.velocity.y});
        }
        return {x:0, y:0};
    }

    // ── FORMATION (spring-damper) ─────────────────────────────────────────────
    formationBehaviour() {
        if (this.slotIndex < 0 || this.slotIndex >= this.legion.slots.length) {
            this.swarmBehaviour(); return;
        }
        const {dx, dy} = this.legion.slots[this.slotIndex];
        const cx = this.legion.x + this.legion.width/2;
        const cy = this.legion.y + this.legion.height/2;
        const wx = cx + dx, wy = cy + dy;
        const dist = Math.hypot(wx - this.position.x, wy - this.position.y);

        const steer  = this.seek({x: wx, y: wy});
        const weight = Math.min(3.5, 1.0 + dist * 0.06);
        this.velocity.x += steer.x * weight;
        this.velocity.y += steer.y * weight;

        if (dist < 14) { this.velocity.x *= 0.84; this.velocity.y *= 0.84; }

        const sep = this.separate(this.legion.units, 10);
        this.velocity.x += sep.x * 0.55;
        this.velocity.y += sep.y * 0.55;

        this.clampSpeed();
    }

    // ── COMBAT (seek & attack nearest enemy) ──────────────────────────────────
    combatBehaviour(enemyLegion) {
        // Re-evaluate target if current target is invalid or dead
        if (!this.combatTarget || this.combatTarget.isDead || this.combatTarget.hp <= 0) {
            const { enemy } = this.findNearestEnemy(enemyLegion);
            this.combatTarget = enemy;
        }

        const target = this.combatTarget;
        if (!target || target.isDead || target.hp <= 0) return;

        const nearDist = Math.hypot(this.position.x - target.position.x, this.position.y - target.position.y);

        if (nearDist <= ENGAGE_RADIUS) {
            const s = this.seek(target.position);
            this.velocity.x += s.x * 3; this.velocity.y += s.y * 3;
            this.clampSpeed();

            if (nearDist <= ATTACK_RANGE && this.attackCooldown <= 0) {
                if (this.team === TEAM.BLUE) {
                    console.log('Blue Attacking:', target);
                } else {
                    console.log('Red Attacking:', target);
                }
                const dmg = Math.max(1, this.attackPower + Math.floor(Math.random() * 5) - 2);
                target.takeDamage(dmg, this);
                this.attackCooldown = ATTACK_INTERVAL;
            }
        } else {
            const sep  = this.separate(allBoids, 20);
            const seek = this.seek(target.position);
            this.velocity.x += sep.x * 1.5 + seek.x * 2;
            this.velocity.y += sep.y * 1.5 + seek.y * 2;
            this.clampSpeed();
        }
    }

    // ── Helpers ───────────────────────────────────────────────────────────────
    seek(t) {
        let dx = t.x - this.position.x, dy = t.y - this.position.y;
        const d = Math.hypot(dx, dy);
        if (d > 0) { dx = (dx/d)*this.maxSpeed; dy = (dy/d)*this.maxSpeed; }
        return this.limitForce({x: dx-this.velocity.x, y: dy-this.velocity.y});
    }
    limitForce(s) {
        const m = Math.hypot(s.x, s.y);
        if (m > this.maxForce) { s.x=(s.x/m)*this.maxForce; s.y=(s.y/m)*this.maxForce; }
        return s;
    }
    clampSpeed() {
        const sp = Math.hypot(this.velocity.x, this.velocity.y);
        if (sp > this.maxSpeed) { this.velocity.x=(this.velocity.x/sp)*this.maxSpeed; this.velocity.y=(this.velocity.y/sp)*this.maxSpeed; }
    }

    draw() {
        if (this.isDead || this.hp <= 0) return;
        const theta = Math.atan2(this.velocity.y, this.velocity.x);
        ctx.save();
        ctx.translate(this.position.x, this.position.y);
        ctx.rotate(theta);
        ctx.beginPath();
        ctx.moveTo(this.size*1.8, 0);
        ctx.lineTo(-this.size, -this.size);
        ctx.lineTo(-this.size,  this.size);
        ctx.closePath();
        ctx.fillStyle   = this.hitFlash > 0 ? '#ffffff' : this.color;
        ctx.shadowBlur  = 6;
        ctx.shadowColor = this.color;
        ctx.fill();
        if (this.hitFlash > 0) this.hitFlash--;
        ctx.restore();

        // HP bar during combat
        if (this.legion.state === 'COMBAT') {
            const bw=18, bh=3;
            const bx=this.position.x - bw/2, by=this.position.y - this.size*2 - 4;
            const pct = Math.max(0, this.hp / BASE_HP);
            ctx.fillStyle = '#1e293b'; ctx.fillRect(bx, by, bw, bh);
            ctx.fillStyle = pct>0.5 ? '#22c55e' : pct>0.25 ? '#eab308' : '#ef4444';
            ctx.fillRect(bx, by, bw*pct, bh);
        }

        // Front-rank white dot (MARCH + formation)
        if (this.legion.formation !== 'SWARM' && this.rank === 0 && this.legion.state === 'MARCH') {
            ctx.beginPath();
            ctx.arc(this.position.x, this.position.y, 1.6, 0, Math.PI*2);
            ctx.fillStyle = 'rgba(255,255,255,0.50)';
            ctx.fill();
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  FALLEN MARKERS
// ═══════════════════════════════════════════════════════════════════════════════
function spawnFallen(x, y)  { fallen.push({x, y}); }

function drawFallen() {
    ctx.fillStyle = '#334155';
    for (const f of fallen) {
        ctx.beginPath(); ctx.arc(f.x, f.y, 2, 0, Math.PI*2); ctx.fill();
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  COMBAT STATE CHECK
// ═══════════════════════════════════════════════════════════════════════════════
function checkCombatState() {
    if (legions.length < 2) return;
    const [la, lb] = legions;
    if (!la.units.length || !lb.units.length) return;

    let triggered = la.overlaps(lb);
    if (!triggered) {
        outer:
        for (const ua of la.units) {
            for (const ub of lb.units) {
                if (Math.hypot(ua.position.x-ub.position.x, ua.position.y-ub.position.y) <= COMBAT_DETECT_PX) {
                    triggered = true; break outer;
                }
            }
        }
    }
    if (triggered) {
        const justStarted = la.state !== 'COMBAT';
        la.state = 'COMBAT'; lb.state = 'COMBAT';
        if (justStarted) { la.assignSlots(lb.center); lb.assignSlots(la.center); }
    }
}


// ═══════════════════════════════════════════════════════════════════════════════
//  VICTORY CHECK
// ═══════════════════════════════════════════════════════════════════════════════
function checkVictory() {
    if (legions.length < 2 || victoryBanner) return;
    const [la, lb] = legions;

    let winner = null;
    if (la.units.length === 0 && lb.units.length > 0) { winner = lb; la.state='MARCH'; lb.state='MARCH'; }
    else if (lb.units.length === 0 && la.units.length > 0) { winner = la; lb.state='MARCH'; la.state='MARCH'; }

    if (winner) {
        winner.state = 'MARCH';
        if (winner.formation !== 'SWARM') {
            winner.assignSlots(null);
        }
        const subtitle = gameMode === 'PVE'
            ? winner.team === TEAM.BLUE ? '🎉 You Win! Click Restart to play again.' : '💀 CPU wins! Click Restart to try again.'
            : 'Click Restart to play again.';
        victoryBanner = { text: `${winner.name} VICTORIOUS`, color: winner.color, alpha: 0, subtitle };
        document.getElementById('restart-btn').style.display = 'block';
    }
}

function drawVictoryBanner() {
    if (!victoryBanner) return;
    victoryBanner.alpha = Math.min(1, victoryBanner.alpha + 0.02);
    const cx = canvas.width/2, cy = canvas.height/2;
    ctx.save();
    ctx.globalAlpha = victoryBanner.alpha * 0.82;
    ctx.fillStyle   = '#0f172a';
    ctx.fillRect(cx-280, cy-65, 560, 130);
    ctx.globalAlpha  = victoryBanner.alpha;
    ctx.strokeStyle  = victoryBanner.color;
    ctx.lineWidth    = 2;
    ctx.shadowBlur   = 24; ctx.shadowColor = victoryBanner.color;
    ctx.strokeRect(cx-280, cy-65, 560, 130);
    ctx.font         = 'bold 36px system-ui,sans-serif';
    ctx.fillStyle    = victoryBanner.color;
    ctx.textAlign    = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(victoryBanner.text, cx, cy - 14);
    ctx.font         = '500 14px system-ui,sans-serif';
    ctx.fillStyle    = '#94a3b8'; ctx.shadowBlur = 0;
    ctx.fillText(victoryBanner.subtitle, cx, cy + 24);
    ctx.restore();
}

// ═══════════════════════════════════════════════════════════════════════════════
//  CPU COMMANDER  ─  runs every CPU_INTERVAL frames
// ═══════════════════════════════════════════════════════════════════════════════
function updateCPUCommander() {
    if (gameMode !== 'PVE') return;
    if (victoryBanner) return;

    const reds  = legions.filter(l => l.team === TEAM.RED && l.units.length > 0);
    const blues = legions.filter(l => l.team === TEAM.BLUE && l.units.length > 0);
    if (!reds.length || !blues.length) return;

    reds.forEach((red, ri) => {
        let target = null, minD = Infinity;
        for (const b of blues) {
            const d = Math.hypot(red.center.x - b.center.x, red.center.y - b.center.y);
            if (d < minD) { minD = d; target = b; }
        }
        if (!target) return;

        const dist = minD;

        // ── CPU STATE LOCKING: If Red Legion is in COMBAT and enemy is within 150px, lock state ──
        if (red.state === 'COMBAT') {
            if (dist <= COMBAT_UNLOCK_PX) {
                // Enemies are close; remain locked in COMBAT mode
                return;
            } else {
                // Enemies retreated far away; unlock back to MARCH mode
                red.state = 'MARCH';
            }
        }

        // Formation decision based on distance
        let newForm = red.formation;
        if      (dist > 200) newForm = 'GRID';
        else if (dist > 100) newForm = 'LINE';

        if (newForm !== red.formation) {
            red.formation = newForm;
            red.assignSlots(target.center);
        }

        // March target
        if (ri === 0) {
            red.targetX = target.center.x;
            red.targetY = target.center.y;
        } else {
            const dx = target.center.x - red.center.x;
            const dy = target.center.y - red.center.y;
            const dm = Math.hypot(dx, dy);
            if (dm > 0) {
                const px = -dy / dm;
                const py =  dx / dm;
                red.targetX = target.center.x + px * 100;
                red.targetY = target.center.y + py * 100;
            }
        }

        cpuActivity = { x: red.center.x, y: red.center.y, alpha: 1.0, radius: 0 };
    });
}

function drawCPUActivity() {
    if (!cpuActivity || gameMode !== 'PVE') return;
    cpuActivity.alpha  -= 0.025;
    cpuActivity.radius += 1.2;
    if (cpuActivity.alpha <= 0) { cpuActivity = null; return; }
    ctx.beginPath();
    ctx.arc(cpuActivity.x, cpuActivity.y, cpuActivity.radius, 0, Math.PI*2);
    ctx.strokeStyle = `rgba(251,191,36,${cpuActivity.alpha * 0.7})`;
    ctx.lineWidth   = 1.5;
    ctx.stroke();
}

// ═══════════════════════════════════════════════════════════════════════════════
//  INIT
// ═══════════════════════════════════════════════════════════════════════════════
function init() {
    legions = []; allBoids = []; fallen = [];
    victoryBanner = null; commandPulse = null; cpuActivity = null;
    cpuTick = 0;

    const bw = 220, bh = 180, midY = (canvas.height - bh) / 2;

    // Legion A – Blue Legion (Player)
    const la = new Legion('legion_a', 'Blue Legion', 100, midY, bw, bh, '#3b82f6', TEAM.BLUE, 50);
    for (let i = 0; i < 50; i++) {
        const b = new Boid(la.x+20+Math.random()*(bw-40), la.y+20+Math.random()*(bh-40), la);
        la.units.push(b); allBoids.push(b);
    }
    legions.push(la);

    // Legion B – Red Legion (CPU in PvE, Player in PvP)
    const sx = Math.max(100, canvas.width - bw - 100);
    const lb = new Legion('legion_b', 'Red Legion', sx, midY, bw, bh, '#ef4444', TEAM.RED, 50);
    for (let i = 0; i < 50; i++) {
        const b = new Boid(lb.x+20+Math.random()*(bw-40), lb.y+20+Math.random()*(bh-40), lb);
        lb.units.push(b); allBoids.push(b);
    }
    legions.push(lb);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  MAIN ANIMATION LOOP
// ═══════════════════════════════════════════════════════════════════════════════
function animate() {
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = 'rgba(15,23,42,0.42)';
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    for (let step = 0; step < simSpeed; step++) {
        // CPU tick
        if (gameMode === 'PVE') {
            cpuTick++;
            if (cpuTick >= CPU_INTERVAL) { cpuTick = 0; updateCPUCommander(); }
        }

        checkCombatState();
        
        const [la, lb] = legions;
        la.update(lb);
        lb.update(la);

        allBoids = legions.flatMap(l => l.units);

        // ── SHUFFLE ALL BOIDS EVERY FRAME TO ELIMINATE ARRAY FIRST-STRIKE BIAS ──
        for (let i = allBoids.length - 1; i > 0; i--) {
            const j = Math.floor(Math.random() * (i + 1));
            [allBoids[i], allBoids[j]] = [allBoids[j], allBoids[i]];
        }

        for (const b of allBoids) {
            if (!b.isDead && b.hp > 0) {
                const enemyLegion = b.legion === la ? lb : la;
                b.tick(enemyLegion);
            }
        }

        checkVictory();
    }

    drawFallen();

    for (const l of legions) l.draw();

    // Command pulse
    if (commandPulse) {
        ctx.beginPath();
        ctx.arc(commandPulse.x, commandPulse.y, commandPulse.radius, 0, Math.PI*2);
        const hex = Math.floor(commandPulse.alpha*255).toString(16).padStart(2,'0');
        ctx.strokeStyle = `${commandPulse.color}${hex}`;
        ctx.lineWidth = 2; ctx.stroke();
        commandPulse.radius += 1.5; commandPulse.alpha -= 0.03;
        if (commandPulse.alpha <= 0) commandPulse = null;
    }

    for (const b of allBoids) b.draw();

    drawCPUActivity();
    drawVictoryBanner();
    requestAnimationFrame(animate);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  FORMATION UI
// ═══════════════════════════════════════════════════════════════════════════════
function updateFormationUI(selectedLegion) {
    const label = document.getElementById('formation-label');
    if (!selectedLegion) {
        label.textContent = gameMode === 'PVE' ? '↑ Select a Blue Legion' : '↑ Select a Legion first';
        document.querySelectorAll('.formation-btn').forEach(b => b.classList.remove('active-a','active-b'));
        return;
    }
    label.textContent = `${selectedLegion.name}:`;
    document.querySelectorAll('.formation-btn').forEach(btn => {
        btn.classList.remove('active-a','active-b');
        if (btn.dataset.formation === selectedLegion.formation)
            btn.classList.add(selectedLegion.team === TEAM.BLUE ? 'active-a' : 'active-b');
    });
}

document.querySelectorAll('.formation-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        const sel = legions.find(l => l.isSelected);
        if (!sel || (gameMode === 'PVE' && sel.team === TEAM.RED)) return;
        sel.formation = btn.dataset.formation;
        sel.assignSlots(legions.find(l => l !== sel)?.center);
        updateFormationUI(sel);
    });
});

// ═══════════════════════════════════════════════════════════════════════════════
//  MODE TOGGLE BUTTONS
// ═══════════════════════════════════════════════════════════════════════════════
document.querySelectorAll('.mode-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        const newMode = btn.dataset.mode;
        if (newMode === gameMode) return;
        gameMode = newMode;

        document.querySelectorAll('.mode-btn').forEach(b => b.classList.remove('active'));
        btn.classList.add('active');

        const hint = document.getElementById('mode-hint');
        hint.textContent = gameMode === 'PVE'
            ? '🔵 You command Blue. Red is CPU-controlled.'
            : '⚔ Both legions are player-controlled.';
        hint.className = gameMode === 'PVE' ? 'mode-hint-pve' : 'mode-hint-pvp';

        legions.forEach(l => { if (l.team === TEAM.RED) l.isSelected = false; });
        updateFormationUI(null);

        document.getElementById('restart-btn').style.display = 'none';
        init();
    });
});

// ═══════════════════════════════════════════════════════════════════════════════
//  SPEED TOGGLE BUTTONS
// ═══════════════════════════════════════════════════════════════════════════════
document.querySelectorAll('.speed-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        simSpeed = parseInt(btn.dataset.speed, 10) || 1;
        document.querySelectorAll('.speed-btn').forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
    });
});

// ═══════════════════════════════════════════════════════════════════════════════
//  RESTART BUTTON
// ═══════════════════════════════════════════════════════════════════════════════
document.getElementById('restart-btn').addEventListener('click', () => {
    document.getElementById('restart-btn').style.display = 'none';
    legions.forEach(l => l.isSelected = false);
    updateFormationUI(null);
    init();
});

// ═══════════════════════════════════════════════════════════════════════════════
//  MOUSE EVENTS
// ═══════════════════════════════════════════════════════════════════════════════
canvas.addEventListener('mousedown', e => {
    if (e.button !== 0) return;
    const mx = e.clientX, my = e.clientY;

    legions.forEach(l => l.isSelected = false);
    let clicked = null;
    for (let i = legions.length-1; i >= 0; i--) {
        if (legions[i].containsPoint(mx, my)) { clicked = legions[i]; break; }
    }

    if (gameMode === 'PVE' && clicked?.team === TEAM.RED) clicked = null;

    if (clicked) {
        clicked.isSelected = true;
        isDragging = true; draggedLegion = clicked;
        dragOffset.x = mx - (clicked.x + clicked.width/2);
        dragOffset.y = my - (clicked.y + clicked.height/2);
        clicked.targetX = mx - dragOffset.x;
        clicked.targetY = my - dragOffset.y;
        updateFormationUI(clicked);
    } else {
        updateFormationUI(null);
    }
});

canvas.addEventListener('mousemove', e => {
    if (isDragging && draggedLegion) {
        if (gameMode === 'PVE' && draggedLegion.team === TEAM.RED) { isDragging=false; draggedLegion=null; return; }
        draggedLegion.targetX = e.clientX - dragOffset.x;
        draggedLegion.targetY = e.clientY - dragOffset.y;
    }
});

window.addEventListener('mouseup', () => { isDragging=false; draggedLegion=null; });

canvas.addEventListener('contextmenu', e => {
    e.preventDefault();
    const sel = legions.find(l => l.isSelected);
    if (!sel || (gameMode === 'PVE' && sel.team === TEAM.RED)) return;
    sel.targetX  = e.clientX; sel.targetY = e.clientY;
    commandPulse = { x: e.clientX, y: e.clientY, radius: 0, alpha: 1, color: sel.color };
});

window.addEventListener('resize', resize);

// ═══════════════════════════════════════════════════════════════════════════════
//  BOOT
// ═══════════════════════════════════════════════════════════════════════════════
init();
animate();
