-- Source:
-- Author: Michael-Keith Bernard
-- Date: August 10, 2012
--
-- Notes: This Trie implementation is a port of the Clojure implementation
-- below. I had to implement quite a few functions from clojure.core to keep the
-- same basic functionality. Probably very little if any of this code is
-- production worthy, but it's interesting all the same. Finally, all of the
-- documentation strings are pulled directly from clojure.core and may not
-- accurately reflect the Lua implementation.
--
-- Also, did I just prove Greenspun's Tenth Rule for Lua? ;)
--
-- Implementation of this Clojure Trie:
--   (defn add-to-trie [trie x]
--     (assoc-in trie x (merge (get-in trie x) {:val x :terminal true})))
--
--   (defn in-trie? [trie x]
--     "Returns true if the value x exists in the specified trie."
--     (:terminal (get-in trie x) false))
--
--   (defn prefix-matches [trie prefix]
--     "Returns a list of matches with the prefix specified in the trie specified."
--     (map-filter :val (tree-seq map? vals (get-in trie prefix))))
--
--   (defn build-trie [coll]
--     "Builds a trie over the values in the specified seq coll."
--     (reduce add-to-trie {} coll))
-- Source: http://stackoverflow.com/questions/1452680/clojure-how-to-generate-a-trie


-- HELPER METHODS --


-- Generic table printing function
-- Source: http://lua-users.org/wiki/TableSerialization
local function table_print (tt, indent, done)
  done = done or {}
  indent = indent or 0
  if type(tt) == "table" then
    for key, value in pairs (tt) do
      io.write(string.rep (" ", indent)) -- indent it
      if type (value) == "table" and not done [value] then
        done [value] = true
        io.write(string.format("[%s] => table\n", tostring (key)));
        io.write(string.rep (" ", indent+4)) -- indent it
        io.write("(\n");
        table_print (value, indent + 7, done)
        io.write(string.rep (" ", indent+4)) -- indent it
        io.write(")\n");
      else
        io.write(string.format("[%s] => %s\n",
            tostring (key), tostring(value)))
      end
    end
  else
    io.write(tt .. "\n")
  end
end

-- Returns its argument.
local function identity(...)
  return ...
end

-- Returns the first logical true value of (pred x) for any x in coll, else nil.
-- One common idiom is to use a set as pred, for example this will return :fred
-- if :fred is in the sequence, otherwise nil: (some #{:fred} coll)
local function some(pred, ts)
  for _, v in pairs(ts) do
    local res = pred(v)
    if res then
      return res
    end
  end
  return false
end

-- Returns true if (pred x) is logical true for every x in coll, else false.
local function every(pred, ts)
  for _, v in pairs(ts) do
    if not pred(v) then
      return false
    end
  end
  return true
end

-- Converts a string into a table
local function letters(word)
  local res = {}
  for i = 1, #word do
    res[#res+1] = word:sub(i,i)
  end
  return res
end

-- Composes f and g such that (f . g)(x) = f(g(x))
local function compose(f, g)
  return function(...)
    return f(g(...))
  end
end

-- f should be a function of 2 arguments. If val is not supplied, returns the
-- result of applying f to the first 2 items in coll, then applying f to that
-- result and the 3rd item, etc. If coll contains no items, f must accept no
-- arguments as well, and reduce returns the result of calling f with no
-- arguments. If coll has only 1 item, it is returned and f is not called. If
-- val is supplied, returns the result of applying f to val and the first item
-- in coll, then applying f to that result and the 2nd item, etc. If coll
-- contains no items, returns val and f is not called.
local function reduce(f, acc, t)
  for _, v in ipairs(t) do
    acc = f(acc, v)
  end
  return acc
end

-- Returns a lazy sequence consisting of the result of applying f to the set of
-- first items of each coll, followed by applying f to the set of second items
-- in each coll, until any one of the colls is exhausted. Any remaining items in
-- other colls are ignored. Function f should accept number-of-colls arguments.
local function map(f, t)
  return reduce(function(memo, e)
    memo[#memo+1] = f(e)
    return memo
  end, {}, t)
end

-- Returns a key v from table t or default if v is not in t.
local function get(t, v, default)
  if not t then return default end
  return t[v] or default
end

-- assoc[iate]. When applied to a map, returns a new map of the same
-- (hashed/sorted) type, that contains the mapping of key(s) to val(s). When
-- applied to a vector, returns a new vector that contains val at index. Note -
-- index must be <= (count vector).
local function assoc(t, k, v)
  t[k] = v
  return t
end

-- Returns the first element of table t
local function first(t)
  return t[1]
end

-- Returns the remaining elements of table t
local function rest(t)
  local res = {}
  for i, v in ipairs(t) do
    if i > 1 then
      res[#res+1] = v
    end
  end
  return res
end

-- conj[oin]. Returns a new collection with the xs 'added'. (conj nil item)
-- returns (item). The 'addition' may happen at different 'places' depending on
-- the concrete type.
local function conj(t1, t2)
  if type(t1) == "table" and type(t2) == "table" then
    for k, v in pairs(t2) do
      t1[k] = v
    end
    return t1
  else
    return nil
  end
end

-- Returns the value in a nested associative structure, where ks is a sequence
-- of ke(ys. Returns nil if the key is not present, or the not-found value if
-- supplied.
local function get_in(t, ks, not_found)
  if not_found == nil then
    return reduce(get, t, ks)
  else
    if #ks == 0 then
      return t
    else
      local v = get(t, first(ks))
      if v == nil then
        --print('not found '..tostring(v))
        return not_found
      else
        --print()
        --table_print(v)
        return get_in(v, rest(ks), not_found)
      end
    end
  end
end

-- Associates a value in a nested associative structure, where ks is a sequence
-- of keys and v is the new value and returns a new nested structure.  If any
-- levels do not exist, hash-maps will be created.
local function assoc_in(t, ks, v)
  local k = first(ks)
  if #ks > 1 then
    return assoc(t, k, assoc_in(get(t, k, {}), rest(ks), v))
  else
    return assoc(t, k, v)
  end
end

-- Returns a map that consists of the rest of the maps conj-ed onto the first.
-- If a key occurs in more than one map, the mapping from the latter
-- (left-to-right) will be the mapping in the result.
local function merge(...)
  local args = { ... }
  if some(identity, args) then
    return reduce(function(memo, t)
      memo = memo or {}
      return conj(memo, t)
    end, first(args), rest(args))
  end
end

-- Trie Implementation --

local function add_to_trie(trie, v)
  return assoc_in(trie, v, merge(get_in(trie, v, {}), {val = v, terminal = true}))
end

local function in_trie(trie, v)
  return get(get_in(trie, v), "terminal", false)
end

local function build_trie(words)
  return reduce(add_to_trie, {}, map(letters, words))
end

-- Beyond this point...
-- Author: David Milum

local function longest_match(trie, w)
  local v = letters(w)
  local t = trie
  local match = ''
  local isTerminal = false
  -- For loop only exists if we
  -- 1. Exhuasted the word itself
  -- 2. Reached a bottom in the trie, note we don't just stop at terminals,
  --    there can be multiple on the way down
  for i, l in ipairs(v) do
    if t[l] == nil then
      -- w is longer than the longest match Nothing below
      break
    end
    t = t[l]
    match = match..l
    isTerminal = t['terminal'] == true
  end
  if isTerminal then
    return match
  end
  return nil
end

local function only_key(t)
  local keyCount = 0
  local onlyKey = nil
  for k, _ in pairs(t) do
    --print(tostring(keyCount)..' '..tostring(k))
    if k ~= 'terminal' then
      keyCount = keyCount + 1
      onlyKey = k
    end
    if keyCount > 1 then
      error("not the only key")
    end
  end
  if onlyKey == nil then
    return nil
  end
  return onlyKey
end

local function is_branch(t)
  local keyCount = 0
  for k, _ in pairs(t) do
    --print(tostring(keyCount)..' '..tostring(k))
    if k ~= 'terminal' then
      keyCount = keyCount + 1
    end
    if keyCount > 1 then
      return true
    end
  end
  return false
end

-- Returns the index character of the last branch
-- AND the longest linear branch at the tail end
local function last_branch(trie, w)
  local v = letters(w)
  local t = trie
  local lastBranchIdx = 0
  local lastBranch = t
  local isBranch = is_branch(t)
  for i, l in ipairs(v) do
    if t[l] == nil then
      -- w is longer than the longest match
      break
    end
    t = t[l]
    if isBranch then
      lastBranchIdx = i
      lastBranch = t
    end
    isBranch = is_branch(t)
  end
  --print()
  --print(table_print(lastBranch))
  return {lastBranchIdx, lastBranch}
  --return string.sub(w, lastBranchIdx)
end

local function findChar(topChar, linearBranch, pattern)
  if is_branch(linearBranch) then
    error("Must pass a linear branch")
  end
  local delta = 0
  -- TODO: it'd be faster to use character ranges I imagine
  if string.match(topChar, pattern) then
    return { delta, linearBranch }
  end

  local nextTop = only_key(linearBranch)
  local nextBranch = linearBranch[nextTop]
  delta = delta + 1
  while nextBranch ~= nil do
    if string.match(nextTop, pattern) then
      return { delta, nextBranch }
    end
    nextTop = only_key(nextBranch)
    nextBranch = nextBranch[nextTop]
    delta = delta + 1
  end

end

local function addToStage(s, k, v)
  if s[k] == nil then
    s[k] = {v}
  else
    table.insert(s[k], v)
  end
end

local function putInStage(s, k, v)
  if s[k] == nil then
    s[k] = {}
  end
  s[k] = v
end

local function build_shortcuts(words)

  -- Maps char to potentially multiple wids at a given stage
  -- Where there are multiple wid's its called a collision
  local stageChars = {}
  stageChars[0] = {}
  stageChars[1] = {}
  stageChars[2] = {}
  stageChars[3] = {}
  stageChars[4] = {}

  -- Maps wid to the longest_branch trie
  local stageBranches = {}
  stageBranches[1] = {}
  stageBranches[2] = {}
  stageBranches[3] = {}
  stageBranches[4] = {}

  -- Maps wid to the index of the stageChar
  local stageIndexes = {}
  stageIndexes[0] = {}
  stageIndexes[1] = {}
  stageIndexes[2] = {}
  stageIndexes[3] = {}
  stageIndexes[4] = {}

  -- Maps wid to the resolution. if the wid was resolved at that stage
  -- 0 if collisions were overcome via branching
  -- A positive integer is used when a resolution could not be achieved
  -- This number can be used to identify collided values
  local stageResolves = {}
  stageResolves[1] = {}
  stageResolves[2] = {}
  stageResolves[3] = {}
  stageResolves[4] = {}

  local stageTries = {}
  stageTries[1] = {}
  stageTries[2] = {}
  stageTries[3] = {}
  stageTries[4] = {}


  -- Search stageChars up through stage
  -- TODO SUPER DUPER INEFFICIENT FOR NO REASON
  local function buildSequences(stage)
    local sequences = {}
    for wid, _ in ipairs(words) do
      sequences[wid] = ''
    end
    for wid, _ in ipairs(words) do
      local lastIdx = -1
      for s=1,stage do

        local idx = stageIndexes[s][wid]
        --for _, idx in ipairs() do
        if idx ~= nil and idx > lastIdx then
          local c = string.sub(words[wid], idx, idx)
          sequences[wid] = sequences[wid]..c
          lastIdx = idx
        end
        --end

        --for c, wids in pairs(stageChars[s]) do
          --for _, widCandidate in ipairs(wids) do
            --if wid == widCandidate then
              --sequences[wid] = sequences[wid]..c
            --end
          --end
        --end
      end
    end
    return sequences
  end

  -- Get wids that are colliding with the given character up to the given stage
  local function filterActualCollisions(stage, wids, c)
    local dupes = {}
    local sequences = buildSequences(stage)
    for _, wid in ipairs(wids) do
      local seq = sequences[wid]
      if dupes[seq] == nil then
        dupes[seq] = false
      elseif dupes[seq] == false then
        dupes[seq] = true
      end
    end
    local collisions = {}
    local notCollisions = {}
    for _, wid in ipairs(wids) do
      local seq = sequences[wid]
      if dupes[seq] == true then
        table.insert(collisions, wid)
      else
        table.insert(notCollisions, wid)
      end
    end
    return { collisions, notCollisions }
  end

  stageTries[1]['']=build_trie(words)
  stageChars[0][''] = {}
  for wid, w in ipairs(words) do
    table.insert(stageChars[0][''], wid)
  end
  for wid, w in ipairs(words) do
    stageIndexes[0][wid] = 1
  end

  -- Every time buildStage runs it expects a trie to be present at stageTries[0]
  local function buildStage(stage, collision, wids)
    --print(string.format('STAGE %d : COLLISION [%s]', stage, collision))
    local trie = stageTries[stage][collision]
    for _, wid in ipairs(wids) do
      local wStart = stageIndexes[stage-1][wid]
      local w = string.sub(words[wid], wStart)

      -- Using the trie, get the last linear branch for the word
      -- idx refers to the character (relative to w) just before
      -- the branch starts
      --
      -- Branch is a linear try with no branches that can be
      -- folowed straight down
      local idx, branch = unpack(last_branch(trie, w))

      -- Adjust the branch down until it starts with an acceptable character
      local delta
      local pattern = '[a-zA-Z0-9]'
      delta, branch = unpack(findChar(string.sub(w, idx, idx), branch, pattern))
      idx = idx + delta

      putInStage(stageBranches[stage], wid, branch)
      -- stage indexes should be relative to word[wid],
      -- arithmetic is easier on 0-based,
      -- so we convert to that and convert back
      putInStage(stageIndexes[stage], wid, (wStart-1) + (idx-1) + 1)
      if idx > 0 then
        -- A mid point has been chosen
        local c = string.sub(w, idx, idx)
        addToStage(stageChars[stage], c, wid)
        --print(string.format('%s ::: %s -- %s -> [%s]', words[wid], w, c, string.sub(w, idx+1)))
      else
        -- The mid point is just the top level, call it done
        putInStage(stageResolves[stage], wid, 0)
      end
    end
    -- For each collision, build out stage+1
    for c, wids in pairs(stageChars[stage]) do
      wids, notCollisions = unpack(filterActualCollisions(stage, wids, c))
      local dupeIdx = 1
      if #wids > 1 then
        local newTrie = {}
        -- start with the window ids that weren't collisions
        local newWids = notCollisions
        for _, wid in ipairs(wids) do
          local collisionCharIdx = stageIndexes[stage][wid]
          local branch = stageBranches[stage][wid]

          if #words[wid] > collisionCharIdx then
            local onlyKeyInBranch = only_key(branch)
            add_to_trie(newTrie, letters(string.sub(words[wid], collisionCharIdx)))
            if stage < 4 then
              table.insert(newWids, wid)
            else
              putInStage(stageResolves[stage], wid, dupeIdx)
              dupeIdx = dupeIdx + 1
            end
          else
            --print('Giving up on '..words[wid])
            putInStage(stageResolves[stage], wid, dupeIdx)
            dupeIdx = dupeIdx + 1
          end
        end
        if stage < 4 then
          stageChars[stage][c] = newWids
          stageTries[stage+1][c] = newTrie
          if #newWids == 1 then
            --print(string.format('All other collisions purged %s, assign %s -> %s', c, words[newWids[1]], c))
          elseif #newWids == 0 then
            -- Seems like this shouldnt be possible
            --print(string.format('All collisions purged for %s', c))
          else
            buildStage(stage+1, c, wids)
          end
        end
      end
    end
  end

  local allWids = {}
  for i=1,#words do
    table.insert(allWids, i)
  end
  buildStage(1, '', allWids)

  local sequences = buildSequences(4)
  -- Represents the total number of times a sequence is repeated
  local sequenceTotals = {}
  -- Sequence counters to be counted up
  local sequenceCounts = {}
  for _, seq in ipairs(sequences) do
    sequenceCounts[seq] = 0
  end
  for _, seq in ipairs(sequences) do
    if sequenceTotals[seq] == nil then
      sequenceTotals[seq] = 1
    else
      sequenceTotals[seq] = sequenceTotals[seq]+1
    end
  end

  local results = {}
  for wid, w in ipairs(words) do
    local res = {}
    res.word = w
    res.idx = {}
    resolveStage = -1
    resolveNum = nil
    sb = ""
    local lastIdx = -1
    for s=1,4 do

      local idx = stageIndexes[s][wid]
      if idx ~= nil and idx > lastIdx then
        res.idx[s] = idx
        lastIdx = idx
      end

      if stageResolves[s][wid] ~= nil then
        resolveStage = s
        resolveNum = stageResolves[s][wid]
        break
      end
    end

    res.seq = sequences[wid]
    if sequenceTotals[res.seq] > 1 then
      seqCount = sequenceCounts[res.seq]
      sequenceCounts[res.seq] = seqCount+1
      res.tie_break = seqCount
    end

    results[wid] = res
  end
  return results
end

local function debugStuff()
  local words = {
    "/home/catbug/.zshrc",
    "nvim/init.vim",
    "nvim/snapshot-2023-04-18.vim",
  }
  print(vim.inspect(build_shortcuts(words)))
end
--debugStuff()

--table_print(build_shortcuts({
  --'btest.go',
  --'bfoo.go',
  --'ftest.go',
  --'ffoo.go',
--}))

--table_print(build_shortcuts({
  --'blah/aa.java',
  --'blah/ffmpeg_runner.java',
  --'go/tsushima/ffmpeg_#runner.go',
  --'go/tsushima/ffmpeg_$vrunner.go',
  --'go/tsushima-go/ffmpeg_vrunner.go',
  --'go/tsushima-go/mystuff.go',
  --'go/tsushima-go/blahfoo.go',
  --'go/tsushima-go/blahvar.go',
  --'go/tsushima-go/blahvr',
  --'go/tsushima-go/blahvr',
--}))

--print(string.sub('hi', 1))

--words = { "abc$g+e", "bcd", "caa", "cab", "cac", "cad", "abcee", "caab"}
--local trie=build_trie(words)
--local w = 'abc$g+e'
--local c, br = table.unpack(last_branch(trie, w))
--print(c)
--local delta, newBr = table.unpack(findChar(string.sub(w, c, c), br))
--print(string.sub(w, c+delta, c+delta))

--w = "caab"
--l = longest_match(trie, w)
--print('REPLACE'..string.sub(w, #l+1))
--end

--print(table_print(get_in(trie, letters("abcf"), {})))

--print(in_trie(trie, letters("abc")))
--print(in_trie(trie, letters("foo")))

local M = {}

M.build_trie = build_trie
M.longest_match = longest_match
M.build_shortcuts = build_shortcuts
M.debugStuff = debugStuff

return M
