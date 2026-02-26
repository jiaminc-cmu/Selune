-- Benchmark: nbody
-- Tests: float arithmetic, table-as-struct access, nested loops, math.sqrt
-- N-Body simulation from the Computer Language Benchmarks Game
-- Models the Sun + 4 gas giants (Jupiter, Saturn, Uranus, Neptune)
local clock = os.clock
local sqrt = math.sqrt
local pi = math.pi

local SOLAR_MASS = 4 * pi * pi
local DAYS_PER_YEAR = 365.24

local function body(x, y, z, vx, vy, vz, mass)
    return {x=x, y=y, z=z, vx=vx, vy=vy, vz=vz, mass=mass}
end

local function new_bodies()
    return {
        -- Sun
        body(0, 0, 0, 0, 0, 0, SOLAR_MASS),
        -- Jupiter
        body(
            4.84143144246472090e+00,
            -1.16032004402742839e+00,
            -1.03622044471123109e-01,
            1.66007664274403694e-03 * DAYS_PER_YEAR,
            7.69901118419740425e-03 * DAYS_PER_YEAR,
            -6.90460016972063023e-05 * DAYS_PER_YEAR,
            9.54791938424326609e-04 * SOLAR_MASS
        ),
        -- Saturn
        body(
            8.34336671824457987e+00,
            4.12479856412430479e+00,
            -4.03523417114321381e-01,
            -2.76742510726862411e-03 * DAYS_PER_YEAR,
            4.99852801234917238e-03 * DAYS_PER_YEAR,
            2.30417297573763929e-05 * DAYS_PER_YEAR,
            2.85885980666130812e-04 * SOLAR_MASS
        ),
        -- Uranus
        body(
            1.28943695621391310e+01,
            -1.51111514016986312e+01,
            -2.23307578892655734e-01,
            2.96460137564761618e-03 * DAYS_PER_YEAR,
            2.37847173959480950e-03 * DAYS_PER_YEAR,
            -2.96589568540237556e-05 * DAYS_PER_YEAR,
            4.36624404335156298e-05 * SOLAR_MASS
        ),
        -- Neptune
        body(
            1.53796971148509165e+01,
            -2.59193146099879641e+01,
            1.79258772950371181e-01,
            2.68067772490389322e-03 * DAYS_PER_YEAR,
            1.62824170038242295e-03 * DAYS_PER_YEAR,
            -9.51592254519715870e-05 * DAYS_PER_YEAR,
            5.15138902046611451e-05 * SOLAR_MASS
        ),
    }
end

local function advance(bodies, nbodies, dt)
    for i = 1, nbodies do
        local bi = bodies[i]
        local bix, biy, biz = bi.x, bi.y, bi.z
        local bivx, bivy, bivz = bi.vx, bi.vy, bi.vz
        local bimass = bi.mass
        for j = i + 1, nbodies do
            local bj = bodies[j]
            local dx = bix - bj.x
            local dy = biy - bj.y
            local dz = biz - bj.z
            local dist2 = dx * dx + dy * dy + dz * dz
            local dist = sqrt(dist2)
            local mag = dt / (dist2 * dist)
            local bjmass = bj.mass
            bivx = bivx - dx * bjmass * mag
            bivy = bivy - dy * bjmass * mag
            bivz = bivz - dz * bjmass * mag
            bj.vx = bj.vx + dx * bimass * mag
            bj.vy = bj.vy + dy * bimass * mag
            bj.vz = bj.vz + dz * bimass * mag
        end
        bi.vx = bivx
        bi.vy = bivy
        bi.vz = bivz
    end
    for i = 1, nbodies do
        local bi = bodies[i]
        bi.x = bi.x + dt * bi.vx
        bi.y = bi.y + dt * bi.vy
        bi.z = bi.z + dt * bi.vz
    end
end

local function energy(bodies, nbodies)
    local e = 0.0
    for i = 1, nbodies do
        local bi = bodies[i]
        local vx, vy, vz = bi.vx, bi.vy, bi.vz
        e = e + 0.5 * bi.mass * (vx * vx + vy * vy + vz * vz)
        for j = i + 1, nbodies do
            local bj = bodies[j]
            local dx = bi.x - bj.x
            local dy = bi.y - bj.y
            local dz = bi.z - bj.z
            local dist = sqrt(dx * dx + dy * dy + dz * dz)
            e = e - bi.mass * bj.mass / dist
        end
    end
    return e
end

local function offset_momentum(bodies, nbodies)
    local px, py, pz = 0, 0, 0
    for i = 1, nbodies do
        local b = bodies[i]
        local m = b.mass
        px = px + b.vx * m
        py = py + b.vy * m
        pz = pz + b.vz * m
    end
    local sun = bodies[1]
    sun.vx = -px / SOLAR_MASS
    sun.vy = -py / SOLAR_MASS
    sun.vz = -pz / SOLAR_MASS
end

local function run()
    local N = 500000
    local bodies = new_bodies()
    local nbodies = #bodies
    offset_momentum(bodies, nbodies)
    local e0 = energy(bodies, nbodies)
    for _ = 1, N do
        advance(bodies, nbodies, 0.01)
    end
    local e1 = energy(bodies, nbodies)
    return e0, e1
end

local t0 = clock()
local e0, e1 = run()
local elapsed = clock() - t0
-- Verify known energy values for correctness
assert(string.format("%.9f", e0) == "-0.169075164", "wrong initial energy: " .. e0)
assert(string.format("%.9f", e1) == "-0.169096567", "wrong final energy: " .. e1)
print(string.format("RESULT: nbody %.6f", elapsed))
