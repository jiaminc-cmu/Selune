-- Benchmark: particle_sim
-- Tests: float arithmetic in tight loops, math.sqrt, conditionals
-- A 2D particle system simulation with gravity, attractors, and wall bouncing.
-- Structured as an outer particle loop calling an inner physics step function,
-- keeping the hot inner loop tight with few live variables.
local clock = os.clock
local sqrt = math.sqrt

-- Inner physics step: compute one attractor pull on a particle
-- Tight loop, few locals, mostly fadd/fmul — the JIT sweet spot
local function attract_and_step(px, py, vx, vy, mass, steps)
    local dt = 0.0005

    for s = 1, steps do
        -- Gravity
        vy = vy - 9.8 * dt

        -- Attractor at (50, 50) with strength proportional to mass
        local dx = 50.0 - px
        local dy = 50.0 - py
        local dist2 = dx * dx + dy * dy + 1.0
        -- Inverse-square attraction (avoid sqrt in hot path for speed)
        local f = 200.0 * mass / (dist2 * dist2)
        vx = vx + dx * f * dt
        vy = vy + dy * f * dt

        -- Second attractor at (25, 75)
        dx = 25.0 - px
        dy = 75.0 - py
        dist2 = dx * dx + dy * dy + 1.0
        f = 150.0 * mass / (dist2 * dist2)
        vx = vx + dx * f * dt
        vy = vy + dy * f * dt

        -- Drag
        vx = vx * 0.9998
        vy = vy * 0.9998

        -- Integrate
        px = px + vx * dt
        py = py + vy * dt

        -- Wall bounce
        if px < 0.0 then px = -px; vx = -vx * 0.8 end
        if px > 100.0 then px = 200.0 - px; vx = -vx * 0.8 end
        if py < 0.0 then py = -py; vy = -vy * 0.8 end
        if py > 100.0 then py = 200.0 - py; vy = -vy * 0.8 end
    end

    return px, py, vx, vy
end

local function run()
    local N = 2000
    local STEPS = 4000

    local energy = 0.0

    for i = 1, N do
        -- Initialize particle from index
        local fi = i * 1.0
        local px0 = (fi * 7.3) % 100.0
        local py0 = (fi * 3.1) % 100.0
        local vx0 = (fi * 0.13) % 40.0 - 20.0
        local vy0 = (fi * 0.17) % 40.0 - 20.0
        local mass = 0.5 + (fi % 10.0) * 0.1

        local px, py, vx, vy = attract_and_step(px0, py0, vx0, vy0, mass, STEPS)

        -- Accumulate kinetic energy for checksum
        energy = energy + 0.5 * mass * (vx * vx + vy * vy)
    end

    return energy
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: particle_sim %.6f", elapsed))
