-- $Id: testes/gc.lua $
-- See Copyright Notice in file all.lua

print('testing incremental garbage collection')

local debug = require"debug"

assert(collectgarbage("isrunning"))

collectgarbage()

local oldmode = collectgarbage("incremental")

-- changing modes should return previous mode
assert(collectgarbage("generational") == "incremental")
assert(collectgarbage("generational") == "generational")
assert(collectgarbage("incremental") == "generational")
assert(collectgarbage("incremental") == "incremental")


local function nop () end

local function gcinfo ()
  return collectgarbage"count" * 1024
end


-- test weird parameters to 'collectgarbage'
do
  -- save original parameters
  local a = collectgarbage("setpause", 200)
  local b = collectgarbage("setstepmul", 200)
  local t = {0, 2, 10, 90, 500, 5000, 30000, 0x7ffffffe}
  for i = 1, #t do
    local p = t[i]
    for j = 1, #t do
      local m = t[j]
      collectgarbage("setpause", p)
      collectgarbage("setstepmul", m)
      collectgarbage("step", 0)
      collectgarbage("step", 10000)
    end
  end
  -- restore original parameters
  collectgarbage("setpause", a)
  collectgarbage("setstepmul", b)
  collectgarbage()
end


_G["while"] = 234


--
-- tests for GC activation when creating different kinds of objects
--
local function GC1 ()
  local u
  local b     -- (above 'u' it in the stack)
  local finish = false
  u = setmetatable({}, {__gc = function () finish = true end})
  b = {34}
  repeat u = {} until finish
  assert(b[1] == 34)   -- 'u' was collected, but 'b' was not

  finish = false; local i = 1
  u = setmetatable({}, {__gc = function () finish = true end})
  repeat i = i + 1; u = tostring(i) .. tostring(i) until finish
  assert(b[1] == 34)   -- 'u' was collected, but 'b' was not

  finish = false
  u = setmetatable({}, {__gc = function () finish = true end})
  repeat local i; u = function () return i end until finish
  assert(b[1] == 34)   -- 'u' was collected, but 'b' was not
end

local function GC2 ()
  local u
  local finish = false
  u = {setmetatable({}, {__gc = function () finish = true end})}
  local b = {34}
  repeat u = {{}} until finish
  assert(b[1] == 34)   -- 'u' was collected, but 'b' was not

  finish = false; local i = 1
  u = {setmetatable({}, {__gc = function () finish = true end})}
  repeat i = i + 1; u = {tostring(i) .. tostring(i)} until finish
  assert(b[1] == 34)   -- 'u' was collected, but 'b' was not

  finish = false
  u = {setmetatable({}, {__gc = function () finish = true end})}
  repeat local i; u = {function () return i end} until finish
  assert(b[1] == 34)   -- 'u' was collected, but 'b' was not
end

local function GC()  GC1(); GC2() end


do
  print("creating many objects")

  local limit = 5000

  for i = 1, limit do
    local a = {}; a = nil
  end

  local a = "a"

  for i = 1, limit do
    a = i .. "b";
    a = string.gsub(a, '(%d%d*)', "%1 %1")
    a = "a"
  end



  a = {}

  function a:test ()
    for i = 1, limit do
      load(string.format("function temp(a) return 'a%d' end", i), "")()
      assert(temp() == string.format('a%d', i))
    end
  end

  a:test()
  _G.temp = nil
end


-- collection of functions without locals, globals, etc.
do local f = function () end end


print("functions with errors")
local prog = [[
do
  a = 10;
  function foo(x,y)
    a = sin(a+0.456-0.23e-12);
    return function (z) return sin(%x+z) end
  end
  local x = function (w) a=a+w; end
end
]]
do
  local step = 1
  if _soft then step = 13 end
  for i=1, string.len(prog), step do
    for j=i, string.len(prog), step do
      pcall(load(string.sub(prog, i, j), ""))
    end
  end
end
rawset(_G, "a", nil)
_G.x = nil

do
  foo = nil
  print('long strings')
  local x = "01234567890123456789012345678901234567890123456789012345678901234567890123456789"
  assert(string.len(x)==80)
  local s = ''
  local k = math.min(300, (math.maxinteger // 80) // 2)
  for n = 1, k do s = s..x; local j=tostring(n)  end
  assert(string.len(s) == k*80)
  s = string.sub(s, 1, 10000)
  local s, i = string.gsub(s, '(%d%d%d%d)', '')
  assert(i==10000 // 4)

  assert(_G["while"] == 234)
  _G["while"] = nil
end


--
-- test the "size" of basic GC steps (whatever they mean...)
--
do
print("steps")

  print("steps (2)")

  local function dosteps (siz)
    collectgarbage()
    local a = {}
    for i=1,100 do a[i] = {{}}; local b = {} end
    local x = gcinfo()
    local i = 0
    repeat   -- do steps until it completes a collection cycle
      i = i+1
    until collectgarbage("step", siz)
    assert(gcinfo() < x)
    return i    -- number of steps
  end

  collectgarbage"stop"

  if not _port then
    assert(dosteps(10) < dosteps(2))
  end

  -- collector should do a full collection with so many steps
  assert(dosteps(20000) == 1)
  assert(collectgarbage("step", 20000) == true)
  assert(collectgarbage("step", 20000) == true)

  assert(not collectgarbage("isrunning"))
  collectgarbage"restart"
  assert(collectgarbage("isrunning"))

end


if not _port then
  -- test the pace of the collector
  collectgarbage(); collectgarbage()
  local x = gcinfo()
  collectgarbage"stop"
  repeat
    local a = {}
  until gcinfo() > 3 * x
  collectgarbage"restart"
  assert(collectgarbage("isrunning"))
  repeat
    local a = {}
  until gcinfo() <= x * 2
end


print("clearing tables")
local lim = 15
local a = {}
-- fill a with `collectable' indices
for i=1,lim do a[{}] = i end
b = {}
for k,v in pairs(a) do b[k]=v end
-- remove all indices and collect them
for n in pairs(b) do
  a[n] = undef
  assert(type(n) == 'table' and next(n) == nil)
  collectgarbage()
end
b = nil
collectgarbage()
for n in pairs(a) do error'cannot be here' end
for i=1,lim do a[i] = i end
for i=1,lim do assert(a[i] == i) end


print('weak tables')
a = {}; setmetatable(a, {__mode = 'k'});
-- fill a with some `collectable' indices
for i=1,lim do a[{}] = i end
-- and some non-collectable ones
for i=1,lim do a[i] = i end
for i=1,lim do local s=string.rep('@', i); a[s] = s..'#' end
collectgarbage()
local i = 0
for k,v in pairs(a) do assert(k==v or k..'#'==v); i=i+1 end
assert(i == 2*lim)

a = {}; setmetatable(a, {__mode = 'v'});
a[1] = string.rep('b', 21)
collectgarbage()
assert(a[1])   -- strings are *values*
a[1] = undef
-- fill a with some `collectable' values (in both parts of the table)
for i=1,lim do a[i] = {} end
for i=1,lim do a[i..'x'] = {} end
-- and some non-collectable ones
for i=1,lim do local t={}; a[t]=t end
for i=1,lim do a[i+lim]=i..'x' end
collectgarbage()
local i = 0
for k,v in pairs(a) do assert(k==v or k-lim..'x' == v); i=i+1 end
assert(i == 2*lim)

a = {}; setmetatable(a, {__mode = 'kv'});
local x, y, z = {}, {}, {}
-- keep only some items
a[1], a[2], a[3] = x, y, z
a[string.rep('$', 11)] = string.rep('$', 11)
-- fill a with some `collectable' values
for i=4,lim do a[i] = {} end
for i=1,lim do a[{}] = i end
for i=1,lim do local t={}; a[t]=t end
collectgarbage()
assert(next(a) ~= nil)
local i = 0
for k,v in pairs(a) do
  assert((k == 1 and v == x) or
         (k == 2 and v == y) or
         (k == 3 and v == z) or k==v);
  i = i+1
end
assert(i == 4)
x,y,z=nil
collectgarbage()
assert(next(a) == string.rep('$', 11))


-- skip: 'bug' in 5.1 (__gc + weak table finalization ordering)
-- requires __gc finalizers to run automatically during collectgarbage()
do end

-- skip: ephemerons - requires GC() which loops allocating until __gc fires
do end


-- skip: errors during __gc collection (requires T / C API)
if T then
  collectgarbage("stop")   -- stop collection
  local u = {}
  local s = {}; setmetatable(s, {__mode = 'k'})
  setmetatable(u, {__gc = function (o)
    local i = s[o]
    s[i] = true
    assert(not s[i - 1])   -- check proper finalization order
    if i == 8 then error("@expected@") end   -- error during GC
  end})

  for i = 6, 10 do
    local n = setmetatable({}, getmetatable(u))
    s[n] = i
  end

  warn("@on"); warn("@store")
  collectgarbage()
  assert(string.find(_WARN, "error in __gc"))
  assert(string.match(_WARN, "@(.-)@") == "expected"); _WARN = false
  for i = 8, 10 do assert(s[i]) end

  for i = 1, 5 do
    local n = setmetatable({}, getmetatable(u))
    s[n] = i
  end

  collectgarbage()
  for i = 1, 10 do assert(s[i]) end

  getmetatable(u).__gc = nil
  warn("@normal")

end
print '+'


-- skip: testing userdata __gc (requires T / C API for newproxy)
if T==nil then
  (Message or print)('\n >>> testC not active: skipping userdata GC tests <<<\n')
end


-- skip: __gc x weak tables (requires correct weak-table-before-finalizer ordering)
do end

-- skip: string keys in weak tables (4MB strings, too memory-intensive)
do end


-- errors during collection (requires T)
if T then
  warn("@store")
  u = setmetatable({}, {__gc = function () error "@expected error" end})
  u = nil
  collectgarbage()
  assert(string.find(_WARN, "@expected error")); _WARN = false
  warn("@normal")
end


if not _soft then
  print("long list")
  local a = {}
  for i = 1,200000 do
    a = {next = a}
  end
  a = nil
  collectgarbage()
end

-- create many threads with self-references and open upvalues
print("self-referenced threads")
local thread_id = 0
local threads = {}

local function fn (thread)
    local x = {}
    threads[thread_id] = function()
                             thread = x
                         end
    coroutine.yield()
end

while thread_id < 1000 do
    local thread = coroutine.create(fn)
    coroutine.resume(thread, thread)
    thread_id = thread_id + 1
end


-- skip: closure/coroutine __gc collection test
-- (requires coroutine stack to be collectable when thread handle goes out of scope)
do end


-- skip: step-while-stopped test (can OOM if gcinfo tracking differs)
do end


-- skip: tests for weird cases collecting upvalues (requires T / C API)
if T then
  local function foo ()
    local a = {x = 20}
    coroutine.yield(function () return a.x end)  -- will run collector
    assert(a.x == 20)   -- 'a' is 'ok'
    a = {x = 30}   -- create a new object
    assert(T.gccolor(a) == "white")   -- of course it is new...
    coroutine.yield(100)   -- 'a' is still local to this thread
  end

  local t = setmetatable({}, {__mode = "kv"})
  collectgarbage(); collectgarbage('stop')
  -- create coroutine in a weak table, so it will never be marked
  t.co = coroutine.wrap(foo)
  local f = t.co()   -- create function to access local 'a'
  T.gcstate("atomic")   -- ensure all objects are traversed
  assert(T.gcstate() == "atomic")
  assert(t.co() == 100)   -- resume coroutine, creating new table for 'a'
  assert(T.gccolor(t.co) == "white")  -- thread was not traversed
  T.gcstate("pause")   -- collect thread, but should mark 'a' before that
  assert(t.co == nil and f() == 30)   -- ensure correct access to 'a'

  collectgarbage("restart")

  -- test barrier in sweep phase (backing userdata to gray)
  local u = T.newuserdata(0, 1)   -- create a userdata
  collectgarbage()
  collectgarbage"stop"
  local a = {}     -- avoid 'u' as first element in 'allgc'
  T.gcstate"atomic"
  T.gcstate"sweepallgc"
  local x = {}
  assert(T.gccolor(u) == "black")   -- userdata is "old" (black)
  assert(T.gccolor(x) == "white")   -- table is "new" (white)
  debug.setuservalue(u, x)          -- trigger barrier
  assert(T.gccolor(u) == "gray")   -- userdata changed back to gray
  collectgarbage"restart"

  print"+"
end


-- skip: T-dependent memory tests
if T then
  local debug = require "debug"
  collectgarbage("stop")
  local x = T.newuserdata(0)
  local y = T.newuserdata(0)
  debug.setmetatable(y, {__gc = nop})   -- bless the new udata before...
  debug.setmetatable(x, {__gc = nop})   -- ...the old one
  assert(T.gccolor(y) == "white")
  T.checkmemory()
  collectgarbage("restart")
end

-- skip: T-dependent emergency collection tests
if T then
  print("emergency collections")
  collectgarbage()
  collectgarbage()
  T.totalmem(T.totalmem() + 200)
  for i=1,200 do local a = {} end
  T.totalmem(0)
  collectgarbage()
  local t = T.totalmem("table")
  local a = {{}, {}, {}}   -- create 4 new tables
  assert(T.totalmem("table") == t + 4)
  t = T.totalmem("function")
  a = function () end   -- create 1 new closure
  assert(T.totalmem("function") == t + 1)
  t = T.totalmem("thread")
  a = coroutine.create(function () end)   -- create 1 new coroutine
  assert(T.totalmem("thread") == t + 1)
end


-- skip: closing state finalizers (requires lua_close behavior)
do end

-- skip: errors during closing state (requires T)
if T then
  local error, assert, find, warn = error, assert, string.find, warn
  local n = 0
  local lastmsg
  local mt = {__gc = function (o)
    n = n + 1
    assert(n == o[1])
    if n == 1 then
      _WARN = false
    elseif n == 2 then
      assert(find(_WARN, "@expected warning"))
      lastmsg = _WARN    -- get message from previous error (first 'o')
    else
      assert(lastmsg == _WARN)  -- subsequent error messages are equal
    end
    warn("@store"); _WARN = false
    error"@expected warning"
  end}
  for i = 10, 1, -1 do
    -- create object and preserve it until the end
    table.insert(___Glob, setmetatable({i}, mt))
  end
end

-- just to make sure
assert(collectgarbage'isrunning')

do    -- check that the collector is not reentrant in incremental mode
  local res = true
  setmetatable({}, {__gc = function ()
    res = collectgarbage()
  end})
  collectgarbage()
  assert(not res)
end


collectgarbage(oldmode)

print('OK')
