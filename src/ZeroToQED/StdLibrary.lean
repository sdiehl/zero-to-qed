import Batteries

/-!
# Standard Library and Batteries

Code examples for IO operations, Batteries, and the package ecosystem.
-/

namespace ZeroToQED.StdLibrary

-- ANCHOR: io_basics
-- Basic IO operations
def ioDemo : IO Unit := do
  -- Print to stdout
  IO.println "Hello, world!"
  IO.print "No newline"
  IO.println ""  -- newline

  -- Environment variables
  let path ← IO.getEnv "PATH"
  IO.println s!"PATH exists: {path.isSome}"

  -- Current time (milliseconds since epoch)
  let now ← IO.monoMsNow
  IO.println s!"Timestamp: {now}"

  -- Random numbers
  let rand ← IO.rand 1 100
  IO.println s!"Random 1-100: {rand}"
-- ANCHOR_END: io_basics

-- ANCHOR: file_io
-- File operations
def fileDemo : IO Unit := do
  let testFile := "test_output.txt"

  -- Write to file
  IO.FS.writeFile testFile "Line 1\nLine 2\nLine 3\n"

  -- Read entire file
  let contents ← IO.FS.readFile testFile
  IO.println s!"Contents:\n{contents}"

  -- Read as lines
  let lines ← IO.FS.lines testFile
  IO.println s!"Number of lines: {lines.size}"
  for line in lines do
    IO.println s!"  > {line}"

  -- Clean up
  IO.FS.removeFile testFile
-- ANCHOR_END: file_io

-- ANCHOR: directory_io
-- Directory operations
def directoryDemo : IO Unit := do
  -- Current working directory
  let cwd ← IO.currentDir
  IO.println s!"Current directory: {cwd}"

  -- List directory contents
  let entries ← System.FilePath.readDir "."
  IO.println s!"Files in current directory: {entries.size}"

  -- Print first few entries
  for entry in entries.toList.take 5 do
    IO.println s!"  {entry.fileName}"
-- ANCHOR_END: directory_io

-- ANCHOR: process_io
-- Running external processes
def processDemo : IO Unit := do
  -- Run a command and capture output
  let output ← IO.Process.output {
    cmd := "echo"
    args := #["Hello from subprocess"]
  }
  IO.println s!"Exit code: {output.exitCode}"
  IO.println s!"stdout: {output.stdout}"

  -- Check if command succeeded
  if output.exitCode == 0 then
    IO.println "Command succeeded"
  else
    IO.println s!"Command failed: {output.stderr}"
-- ANCHOR_END: process_io

-- ANCHOR: batteries_heap
-- BinaryHeap: priority queue with O(log n) push/pop
def heapDemo : IO Unit := do
  -- Max-heap (largest first with >)
  let heap := Batteries.BinaryHeap.empty (α := Nat) (lt := (· > ·))
    |>.insert 5
    |>.insert 1
    |>.insert 3
    |>.insert 9

  IO.println s!"heap max: {heap.max}"  -- some 9

  -- Pop the max element
  let (maxVal, heap') := heap.extractMax
  IO.println s!"extracted: {maxVal}"   -- some 9
  IO.println s!"new max: {heap'.max}"  -- some 5
-- ANCHOR_END: batteries_heap

-- ANCHOR: batteries_rbmap
-- RBMap: ordered map with O(log n) operations
def rbmapDemo : IO Unit := do
  -- Create a map with String keys, Nat values
  let scores : Batteries.RBMap String Nat compare :=
    Batteries.RBMap.empty
      |>.insert "alice" 95
      |>.insert "bob" 87
      |>.insert "carol" 92

  -- Lookup
  let aliceScore := scores.find? "alice"
  let daveScore := scores.find? "dave"
  IO.println s!"alice: {aliceScore}"  -- some 95
  IO.println s!"dave: {daveScore}"    -- none

  -- Convert to list for display (sorted by key)
  IO.println s!"all: {scores.toList}"
-- ANCHOR_END: batteries_rbmap

-- ANCHOR: batteries_unionfind
-- UnionFind: disjoint set with near O(1) union/find
def unionFindDemo : IO Unit := do
  -- Create structure and add 5 elements (indices 0-4)
  let uf := Batteries.UnionFind.empty
    |>.push |>.push |>.push |>.push |>.push

  -- Union 0 with 1, and 2 with 3
  let uf := uf.union! 0 1
  let uf := uf.union! 2 3

  -- Check if elements are in same set (same root)
  let root0 := uf.rootD 0
  let root1 := uf.rootD 1
  let root2 := uf.rootD 2
  let root4 := uf.rootD 4

  IO.println s!"0 and 1 same set: {root0 == root1}"  -- true
  IO.println s!"0 and 2 same set: {root0 == root2}"  -- false
  IO.println s!"4 alone: {root4 == 4}"               -- true
-- ANCHOR_END: batteries_unionfind

-- ANCHOR: batteries_dlist
-- DList: difference list with O(1) append
def dlistDemo : IO Unit := do
  -- Build a list by repeated appending
  -- With regular List, this would be O(n^2), with DList it's O(n)
  let d1 : Batteries.DList Nat := Batteries.DList.singleton 1
  let d2 := d1.push 2
  let d3 := d2.push 3
  let d4 := d3.append (Batteries.DList.ofList [4, 5, 6])

  -- Convert back to List when done building
  let result := d4.toList
  IO.println s!"result: {result}"  -- [1, 2, 3, 4, 5, 6]
-- ANCHOR_END: batteries_dlist

-- ANCHOR: batteries_list_array
-- Batteries extends List and Array with useful functions
def batteriesListDemo : IO Unit := do
  let nums := [1, 2, 3, 4, 5]

  -- Chunking
  let chunks := nums.toChunks 2
  IO.println s!"toChunks 2: {chunks}"   -- [[1, 2], [3, 4], [5]]

  -- Rotating
  let rotL := nums.rotateLeft 2
  let rotR := nums.rotateRight 2
  IO.println s!"rotateLeft 2: {rotL}"   -- [3, 4, 5, 1, 2]
  IO.println s!"rotateRight 2: {rotR}"  -- [4, 5, 1, 2, 3]

  -- Partitioning
  let (small, big) := nums.partition (· ≤ 3)
  IO.println s!"partition: small={small}, big={big}"

  -- Erasure (remove first occurrence)
  let erased := nums.erase 3
  IO.println s!"erase 3: {erased}"       -- [1, 2, 4, 5]

  -- Running accumulations (scanl from the left, scanr from the right)
  IO.println s!"scanl (+) 0: {nums.scanl (· + ·) 0}"   -- [0, 1, 3, 6, 10, 15]
  IO.println s!"scanr (+) 0: {nums.scanr (· + ·) 0}"   -- [15, 14, 12, 9, 5, 0]

  -- Extrema by a key function (the proof shows the list is non-empty)
  let words := ["a", "ccc", "bb"]
  IO.println s!"maxOn length: {words.maxOn String.length (by decide)}"  -- ccc
  IO.println s!"minOn length: {words.minOn String.length (by decide)}"  -- a
-- ANCHOR_END: batteries_list_array

-- ANCHOR: std_hashmap
-- HashMap: O(1) average insert/lookup
def hashmapDemo : IO Unit := do
  -- Create a HashMap from key-value pairs
  let mut scores : Std.HashMap String Nat := {}
  scores := scores.insert "alice" 95
  scores := scores.insert "bob" 87
  scores := scores.insert "carol" 92

  -- Lookup with get?
  let aliceScore := scores.get? "alice"
  IO.println s!"alice: {aliceScore}"  -- some 95

  -- Check membership
  IO.println s!"contains bob: {scores.contains "bob"}"  -- true

  -- Get with default
  let daveScore := scores.getD "dave" 0
  IO.println s!"dave (default 0): {daveScore}"  -- 0

  -- Iterate over entries
  IO.println "All scores:"
  for (name, score) in scores do
    IO.println s!"  {name}: {score}"
-- ANCHOR_END: std_hashmap

-- ANCHOR: std_hashset
-- HashSet: O(1) average membership testing
def hashsetDemo : IO Unit := do
  -- Create a HashSet
  let mut seen : Std.HashSet String := {}
  seen := seen.insert "apple"
  seen := seen.insert "banana"
  seen := seen.insert "cherry"

  IO.println s!"contains apple: {seen.contains "apple"}"    -- true
  IO.println s!"contains grape: {seen.contains "grape"}"    -- false
  IO.println s!"size: {seen.size}"                          -- 3

  -- Set operations
  let more : Std.HashSet String := Std.HashSet.ofList ["banana", "date", "elderberry"]
  let combined := seen.union more
  IO.println s!"union size: {combined.size}"                -- 5
-- ANCHOR_END: std_hashset

-- ANCHOR: std_treemap
-- TreeMap: ordered map with O(log n) operations
def treemapDemo : IO Unit := do
  -- TreeMap keeps keys sorted
  let mut prices : Std.TreeMap String Nat := {}
  prices := prices.insert "banana" 120
  prices := prices.insert "apple" 100
  prices := prices.insert "cherry" 300

  -- Iteration is in sorted order
  IO.println "Prices (sorted by name):"
  for (fruit, price) in prices do
    IO.println s!"  {fruit}: {price}"

  -- Size and membership
  IO.println s!"size: {prices.size}"
  IO.println s!"contains apple: {prices.contains "apple"}"
-- ANCHOR_END: std_treemap

-- ANCHOR: std_time
-- Time: dates, times, and durations
def timeDemo : IO Unit := do
  -- Get current time
  let now ← IO.monoNanosNow
  IO.println s!"Monotonic nanoseconds: {now}"

  -- Durations
  let oneSecond := 1000000000  -- nanoseconds
  let elapsed := now % oneSecond
  IO.println s!"Nanoseconds into current second: {elapsed}"

  -- For wall-clock time, use IO.getNumHeartbeats or external libraries
  let heartbeats ← IO.getNumHeartbeats
  IO.println s!"Heartbeats: {heartbeats}"
-- ANCHOR_END: std_time

-- ANCHOR: std_parsec
-- Parsec: parser combinators for parsing text
open Std.Internal.Parsec String in
def parsecDemo : IO Unit := do
  -- Parser for a natural number
  let parseNat : Parser Nat := digits

  -- Parser for a word (one or more ASCII letters)
  let parseWord : Parser String := many1Chars asciiLetter

  -- Parser for comma-separated numbers
  let parseNumList : Parser (List Nat) := do
    let first ← parseNat
    let rest ← many (skipChar ',' *> parseNat)
    pure (first :: rest.toList)

  -- Run parsers
  match parseNat.run "12345" with
  | .ok n => IO.println s!"Number: {n}"       -- 12345
  | .error e => IO.println s!"Error: {e}"

  match parseWord.run "hello123" with
  | .ok s => IO.println s!"Word: {s}"         -- "hello"
  | .error e => IO.println s!"Error: {e}"

  match parseNumList.run "1,23,456" with
  | .ok ns => IO.println s!"List: {ns}"       -- [1, 23, 456]
  | .error e => IO.println s!"Error: {e}"
-- ANCHOR_END: std_parsec

-- ANCHOR: practical_example
-- Practical example: word frequency counter
def countWords (text : String) : Std.HashMap String Nat :=
  let words := text.toLower.splitOn " "
    |>.map (fun w => w.toList.filter Char.isAlpha |> String.ofList)
    |>.filter (!·.isEmpty)
  words.foldl (fun map word =>
    map.insert word ((map.get? word).getD 0 + 1)
  ) {}

def wordFreqDemo : IO Unit := do
  let text := "The quick brown fox jumps over the lazy dog The dog barks"
  let freq := countWords text

  IO.println "Word frequencies:"
  let sorted := freq.toList.toArray
    |>.qsort (fun a b => a.2 > b.2)

  for (word, count) in sorted do
    IO.println s!"  {word}: {count}"
-- ANCHOR_END: practical_example

def main : IO Unit := do
  IO.println "=== IO Basics ==="
  ioDemo
  IO.println "=== File IO ==="
  fileDemo
  IO.println "=== Directory IO ==="
  directoryDemo
  IO.println "=== Process IO ==="
  processDemo
  IO.println "=== HashMap ==="
  hashmapDemo
  IO.println "=== HashSet ==="
  hashsetDemo
  IO.println "=== TreeMap ==="
  treemapDemo
  IO.println "=== Time ==="
  timeDemo
  IO.println "=== Parsec ==="
  parsecDemo
  IO.println "=== BinaryHeap ==="
  heapDemo
  IO.println "=== RBMap ==="
  rbmapDemo
  IO.println "=== UnionFind ==="
  unionFindDemo
  IO.println "=== DList ==="
  dlistDemo
  IO.println "=== List Extensions ==="
  batteriesListDemo
  IO.println "=== Word Frequency ==="
  wordFreqDemo

end ZeroToQED.StdLibrary
