-- Adapter script to run individual Lua 5.4 test files
-- Sets up the globals expected by the test suite

-- Pretend _port = true to skip platform-specific tests
_port = true
-- Skip soft tests initially
_soft = true
-- Suppress non-performed test messages
_nomsg = true

-- T is not available (no internal C API tests)
T = nil

-- Run the specified test file
local testfile = arg[1]
if not testfile then
  print("Usage: selune run_test.lua <testfile>")
  return
end

-- Set package.path so require can find test helper files
-- Include both the test directory and cwd
local dir = string.match(testfile, "(.-)[^/]*$") or "./"
package.path = dir .. "?.lua;" .. dir .. "?;./?.lua;./?"

local ok, err = pcall(dofile, testfile)
if ok then
  print("PASS: " .. testfile)
else
  print("FAIL: " .. testfile)
  print("  " .. tostring(err))
  os.exit(1)
end
