-- Benchmark: raytracer
-- Tests: table-as-struct, float arithmetic, math.sqrt, recursive calls,
--        conditional branching, function calls, constructors
-- Simplified "Ray Tracing in One Weekend" path tracer in pure Lua
local clock = os.clock
local sqrt = math.sqrt
local abs = math.abs
local floor = math.floor
local huge = math.huge

-- Deterministic RNG (linear congruential, fixed seed)
local rng_state = 1234567
local function random()
    rng_state = (rng_state * 1103515245 + 12345) % 2147483648
    return rng_state / 2147483648
end

local function random_range(mn, mx)
    return mn + (mx - mn) * random()
end

------------------------------------------------------------------------
-- Vec3: {[1]=x, [2]=y, [3]=z} — array indices for fast GetI/SetI
------------------------------------------------------------------------
local function vec3(x, y, z)
    return {x, y, z}
end

local function vec3_add(a, b)
    return {a[1] + b[1], a[2] + b[2], a[3] + b[3]}
end

local function vec3_sub(a, b)
    return {a[1] - b[1], a[2] - b[2], a[3] - b[3]}
end

local function vec3_mul(a, t)
    return {a[1] * t, a[2] * t, a[3] * t}
end

local function vec3_mul_vec(a, b)
    return {a[1] * b[1], a[2] * b[2], a[3] * b[3]}
end

local function vec3_div(a, t)
    local inv = 1.0 / t
    return {a[1] * inv, a[2] * inv, a[3] * inv}
end

local function vec3_dot(a, b)
    return a[1] * b[1] + a[2] * b[2] + a[3] * b[3]
end

local function vec3_cross(a, b)
    return {
        a[2] * b[3] - a[3] * b[2],
        a[3] * b[1] - a[1] * b[3],
        a[1] * b[2] - a[2] * b[1]
    }
end

local function vec3_length_squared(v)
    return v[1] * v[1] + v[2] * v[2] + v[3] * v[3]
end

local function vec3_length(v)
    return sqrt(v[1] * v[1] + v[2] * v[2] + v[3] * v[3])
end

local function vec3_unit(v)
    local len = sqrt(v[1] * v[1] + v[2] * v[2] + v[3] * v[3])
    local inv = 1.0 / len
    return {v[1] * inv, v[2] * inv, v[3] * inv}
end

local function vec3_near_zero(v)
    local s = 1e-8
    return abs(v[1]) < s and abs(v[2]) < s and abs(v[3]) < s
end

local function vec3_reflect(v, n)
    local d = 2.0 * vec3_dot(v, n)
    return {v[1] - d * n[1], v[2] - d * n[2], v[3] - d * n[3]}
end

local function vec3_refract(uv, n, etai_over_etat)
    local cos_theta = -vec3_dot(uv, n)
    if cos_theta > 1.0 then cos_theta = 1.0 end
    local r_out_perp = {
        etai_over_etat * (uv[1] + cos_theta * n[1]),
        etai_over_etat * (uv[2] + cos_theta * n[2]),
        etai_over_etat * (uv[3] + cos_theta * n[3])
    }
    local perp_sq = vec3_length_squared(r_out_perp)
    local factor = -sqrt(abs(1.0 - perp_sq))
    return {
        r_out_perp[1] + factor * n[1],
        r_out_perp[2] + factor * n[2],
        r_out_perp[3] + factor * n[3]
    }
end

local function random_in_unit_sphere()
    while true do
        local x = random_range(-1, 1)
        local y = random_range(-1, 1)
        local z = random_range(-1, 1)
        if x * x + y * y + z * z < 1.0 then
            return {x, y, z}
        end
    end
end

local function random_unit_vector()
    return vec3_unit(random_in_unit_sphere())
end

local function random_in_unit_disk()
    while true do
        local x = random_range(-1, 1)
        local y = random_range(-1, 1)
        if x * x + y * y < 1.0 then
            return {x, y, 0}
        end
    end
end

------------------------------------------------------------------------
-- Ray: {origin, direction}
------------------------------------------------------------------------
local function ray_at(r, t)
    local o, d = r[1], r[2]
    return {o[1] + t * d[1], o[2] + t * d[2], o[3] + t * d[3]}
end

------------------------------------------------------------------------
-- Sphere hit testing
------------------------------------------------------------------------
local function hit_sphere(center, radius, ray_orig, ray_dir, t_min, t_max)
    local ocx = ray_orig[1] - center[1]
    local ocy = ray_orig[2] - center[2]
    local ocz = ray_orig[3] - center[3]
    local a = ray_dir[1] * ray_dir[1] + ray_dir[2] * ray_dir[2] + ray_dir[3] * ray_dir[3]
    local half_b = ocx * ray_dir[1] + ocy * ray_dir[2] + ocz * ray_dir[3]
    local c = ocx * ocx + ocy * ocy + ocz * ocz - radius * radius
    local discriminant = half_b * half_b - a * c
    if discriminant < 0 then return nil end

    local sqrtd = sqrt(discriminant)
    local root = (-half_b - sqrtd) / a
    if root < t_min or root > t_max then
        root = (-half_b + sqrtd) / a
        if root < t_min or root > t_max then
            return nil
        end
    end

    local px = ray_orig[1] + root * ray_dir[1]
    local py = ray_orig[2] + root * ray_dir[2]
    local pz = ray_orig[3] + root * ray_dir[3]
    local inv_r = 1.0 / radius
    local nx = (px - center[1]) * inv_r
    local ny = (py - center[2]) * inv_r
    local nz = (pz - center[3]) * inv_r
    -- Determine front face
    local front = (ray_dir[1] * nx + ray_dir[2] * ny + ray_dir[3] * nz) < 0
    if not front then
        nx, ny, nz = -nx, -ny, -nz
    end
    return root, {px, py, pz}, {nx, ny, nz}, front
end

------------------------------------------------------------------------
-- Materials
------------------------------------------------------------------------
-- Material types: 1=Lambertian, 2=Metal, 3=Dielectric
local MAT_LAMBERTIAN = 1
local MAT_METAL = 2
local MAT_DIELECTRIC = 3

local function reflectance(cosine, ref_idx)
    -- Schlick's approximation
    local r0 = (1 - ref_idx) / (1 + ref_idx)
    r0 = r0 * r0
    return r0 + (1 - r0) * (1 - cosine) ^ 5
end

local function scatter(mat, ray_dir, hit_point, hit_normal, front_face)
    local mtype = mat[1]
    if mtype == MAT_LAMBERTIAN then
        local target = random_unit_vector()
        local scatter_dir = {
            hit_normal[1] + target[1],
            hit_normal[2] + target[2],
            hit_normal[3] + target[3]
        }
        if vec3_near_zero(scatter_dir) then
            scatter_dir = hit_normal
        end
        -- scattered ray: {hit_point, scatter_dir}, attenuation: mat[2]
        return scatter_dir, mat[2]
    elseif mtype == MAT_METAL then
        local reflected = vec3_reflect(vec3_unit(ray_dir), hit_normal)
        local fuzz = mat[3] -- fuzz factor
        if fuzz > 0 then
            local rv = random_in_unit_sphere()
            reflected = {
                reflected[1] + fuzz * rv[1],
                reflected[2] + fuzz * rv[2],
                reflected[3] + fuzz * rv[3]
            }
        end
        if vec3_dot(reflected, hit_normal) > 0 then
            return reflected, mat[2]
        end
        return nil, nil -- absorbed
    else -- MAT_DIELECTRIC
        local ir = mat[2] -- index of refraction
        local ratio = front_face and (1.0 / ir) or ir
        local unit_dir = vec3_unit(ray_dir)
        local cos_theta = -vec3_dot(unit_dir, hit_normal)
        if cos_theta > 1.0 then cos_theta = 1.0 end
        local sin_theta = sqrt(1.0 - cos_theta * cos_theta)
        local cannot_refract = ratio * sin_theta > 1.0

        local direction
        if cannot_refract or reflectance(cos_theta, ratio) > random() then
            direction = vec3_reflect(unit_dir, hit_normal)
        else
            direction = vec3_refract(unit_dir, hit_normal, ratio)
        end
        return direction, {1.0, 1.0, 1.0}
    end
end

------------------------------------------------------------------------
-- World: list of {center, radius, material}
------------------------------------------------------------------------
local function hit_world(world, nobj, ray_orig, ray_dir, t_min, t_max)
    local closest_t = t_max
    local closest_point, closest_normal, closest_front, closest_mat
    for i = 1, nobj do
        local obj = world[i]
        local t, point, normal, front = hit_sphere(
            obj[1], obj[2], ray_orig, ray_dir, t_min, closest_t)
        if t then
            closest_t = t
            closest_point = point
            closest_normal = normal
            closest_front = front
            closest_mat = obj[3]
        end
    end
    return closest_t < t_max, closest_point, closest_normal, closest_front, closest_mat
end

------------------------------------------------------------------------
-- Ray color (recursive path tracing)
------------------------------------------------------------------------
local function ray_color(ray_orig, ray_dir, world, nobj, depth)
    if depth <= 0 then
        return {0, 0, 0}
    end

    local hit, point, normal, front, mat = hit_world(
        world, nobj, ray_orig, ray_dir, 0.001, huge)

    if hit then
        local scatter_dir, attenuation = scatter(mat, ray_dir, point, normal, front)
        if scatter_dir then
            local child = ray_color(point, scatter_dir, world, nobj, depth - 1)
            return {
                attenuation[1] * child[1],
                attenuation[2] * child[2],
                attenuation[3] * child[3]
            }
        end
        return {0, 0, 0}
    end

    -- Sky gradient
    local unit = vec3_unit(ray_dir)
    local t = 0.5 * (unit[2] + 1.0)
    local omt = 1.0 - t
    return {
        omt * 1.0 + t * 0.5,
        omt * 1.0 + t * 0.7,
        omt * 1.0 + t * 1.0
    }
end

------------------------------------------------------------------------
-- Camera
------------------------------------------------------------------------
local function make_camera(lookfrom, lookat, vup, vfov, aspect_ratio, aperture, focus_dist)
    local theta = vfov * 3.14159265358979323846 / 180.0
    local h = 2.0 * (theta / 2.0)  -- tan approximation for small angles
    -- Use actual tan via sin/cos
    local half = theta * 0.5
    -- For the benchmark we use a precomputed tan since Lua has no math.tan in 5.4 without extensions
    -- tan(x) = sin(x)/cos(x), but we'll use a Taylor-series-free approach:
    -- Actually Lua 5.4 doesn't have math.tan, use the identity
    local sin_half = math.sin(half)
    local cos_half = math.cos(half)
    h = sin_half / cos_half  -- tan(half)
    local viewport_height = 2.0 * h
    local viewport_width = aspect_ratio * viewport_height

    local w = vec3_unit(vec3_sub(lookfrom, lookat))
    local u = vec3_unit(vec3_cross(vup, w))
    local v = vec3_cross(w, u)

    local horizontal = vec3_mul(u, focus_dist * viewport_width)
    local vertical = vec3_mul(v, focus_dist * viewport_height)
    local lower_left = vec3_sub(
        vec3_sub(vec3_sub(lookfrom, vec3_div(horizontal, 2)),
                 vec3_div(vertical, 2)),
        vec3_mul(w, focus_dist))

    return {
        origin = lookfrom,
        lower_left = lower_left,
        horizontal = horizontal,
        vertical = vertical,
        u = u,
        v = v,
        lens_radius = aperture / 2.0,
    }
end

local function camera_get_ray(cam, s, t)
    local rd = random_in_unit_disk()
    local offset_u = cam.lens_radius * rd[1]
    local offset_v = cam.lens_radius * rd[2]
    local origin = {
        cam.origin[1] + offset_u * cam.u[1] + offset_v * cam.v[1],
        cam.origin[2] + offset_u * cam.u[2] + offset_v * cam.v[2],
        cam.origin[3] + offset_u * cam.u[3] + offset_v * cam.v[3]
    }
    local dir = {
        cam.lower_left[1] + s * cam.horizontal[1] + t * cam.vertical[1] - origin[1],
        cam.lower_left[2] + s * cam.horizontal[2] + t * cam.vertical[2] - origin[2],
        cam.lower_left[3] + s * cam.horizontal[3] + t * cam.vertical[3] - origin[3]
    }
    return origin, dir
end

------------------------------------------------------------------------
-- Build scene
------------------------------------------------------------------------
local function build_scene()
    local world = {}
    local n = 0

    -- Ground
    n = n + 1
    world[n] = {{0, -1000, 0}, 1000, {MAT_LAMBERTIAN, {0.5, 0.5, 0.5}}}

    -- Small random spheres
    for a = -5, 5 do
        for b = -5, 5 do
            local choose_mat = random()
            local cx = a + 0.9 * random()
            local cy = 0.2
            local cz = b + 0.9 * random()
            -- Don't place too close to main spheres
            local dx = cx - 4
            local dz = cz
            if sqrt(dx * dx + 0.04 + dz * dz) > 0.9 then
                n = n + 1
                if choose_mat < 0.6 then
                    -- Diffuse
                    local r1, g1, b1 = random() * random(), random() * random(), random() * random()
                    world[n] = {{cx, cy, cz}, 0.2, {MAT_LAMBERTIAN, {r1, g1, b1}}}
                elseif choose_mat < 0.85 then
                    -- Metal
                    local r1 = random_range(0.5, 1)
                    local g1 = random_range(0.5, 1)
                    local b1 = random_range(0.5, 1)
                    local fuzz = random_range(0, 0.5)
                    world[n] = {{cx, cy, cz}, 0.2, {MAT_METAL, {r1, g1, b1}, fuzz}}
                else
                    -- Glass
                    world[n] = {{cx, cy, cz}, 0.2, {MAT_DIELECTRIC, 1.5}}
                end
            end
        end
    end

    -- Three main spheres
    n = n + 1
    world[n] = {{0, 1, 0}, 1.0, {MAT_DIELECTRIC, 1.5}}
    n = n + 1
    world[n] = {{-4, 1, 0}, 1.0, {MAT_LAMBERTIAN, {0.4, 0.2, 0.1}}}
    n = n + 1
    world[n] = {{4, 1, 0}, 1.0, {MAT_METAL, {0.7, 0.6, 0.5}, 0.0}}

    return world, n
end

------------------------------------------------------------------------
-- Main render
------------------------------------------------------------------------
local function run()
    -- Image
    local image_width = 80
    local image_height = 45
    local samples_per_pixel = 10
    local max_depth = 10

    -- Camera
    local lookfrom = vec3(13, 2, 3)
    local lookat = vec3(0, 0, 0)
    local vup = vec3(0, 1, 0)
    local aspect_ratio = image_width / image_height
    local cam = make_camera(lookfrom, lookat, vup, 20.0, aspect_ratio, 0.1, 10.0)

    -- Scene
    local world, nobj = build_scene()

    -- Render
    local checksum = 0
    local inv_samples = 1.0 / samples_per_pixel

    for j = image_height - 1, 0, -1 do
        for i = 0, image_width - 1 do
            local r, g, b = 0.0, 0.0, 0.0
            for _ = 1, samples_per_pixel do
                local u = (i + random()) / (image_width - 1)
                local v = (j + random()) / (image_height - 1)
                local ray_orig, ray_dir = camera_get_ray(cam, u, v)
                local color = ray_color(ray_orig, ray_dir, world, nobj, max_depth)
                r = r + color[1]
                g = g + color[2]
                b = b + color[3]
            end
            -- Average and gamma correct (sqrt for gamma 2)
            r = sqrt(r * inv_samples)
            g = sqrt(g * inv_samples)
            b = sqrt(b * inv_samples)
            -- Clamp to [0,1]
            if r > 1.0 then r = 1.0 end
            if g > 1.0 then g = 1.0 end
            if b > 1.0 then b = 1.0 end
            -- Convert to 0-255
            local ir = floor(255.99 * r)
            local ig = floor(255.99 * g)
            local ib = floor(255.99 * b)
            checksum = checksum + ir + ig + ib
        end
    end

    return checksum
end

local t0 = clock()
local checksum = run()
local elapsed = clock() - t0
-- Checksum should be around 1702000-1703000 (minor float rounding differences between implementations)
assert(checksum > 1700000 and checksum < 1710000, "wrong checksum: " .. checksum)
print(string.format("RESULT: raytracer %.6f", elapsed))
