
# Grading Tool

A browser-based tool to assist with grading source code files.
Special support for Racket files


## Problem
- TAing for large classes involves a lot of grading.
- Detailed feedback is desirable.
- Being consistent with scoring requires maintaining a mental database of submissions, attributes and scores.
- Despite the typically high similarity between submissions, the sheer amount of work limits the depth of feedback.

- Many problems have multiple valid approaches, so a single answer key is insufficient.

- For source code, merely measuring the pass-rate of an automated test suite is insufficient.
  A small typo that affects every problem should *not* result in a zero.

- Practically all source code submissions are in CFG languages - ordinary text search tools are insufficient.
  Also, there is a wide variation in formatting
  - some formatting is even misleading.

- Some problems build on previous problems
  the score for that section may be dependent on the previous problem's attributes


## Goals, Assertions
- Many of these assignments are identical between students.
- Identical submissions should get identical scores.
- Submissions with the same flaws should receive the same feedback



## FEATURE LIST:
- interface for categorizing (subsections of) submissions
  - by syntactic equality (lexical level, automatic)
    - per-language (just Racket/Scheme for now)
  - by semantic equality (manual / interactive)
  - then grading can be done on the equivalence classes
    - fewer instances to grade
    - easier to be consistent
- get comments for student 
  - semantic-group-based
    - with file-specific identifiers
  - student-specific
  - copy-to-clipboard
- save and restore sessions as JSON


### stretchgoals / future work:
- improve UI.
  - ideally, a system like VSCode where you can rearrange freely
  - button to copy comments to clipboard
- formatting
  - toggle original and formatted view
- AST-aware highlighting
  - more intelligent than just regex-based
  - for instance, symbols in '() that are normally 
    macros/keywords should not be highlighted as such
- PDF support
  - the other primary form of submissions.
  - select slices
    - if recognizable text present, use that to suggest groupings?
      - very weak though
    - far, far goal is OCR
- upload test results for each submission, other data
  - can group on those too
- with server - host submissions on the server,
  - use git for version control (may need to change files while grading)
  https://stackoverflow.com/questions/3701404/how-to-list-all-commits-that-changed-a-specific-file
- refactor to be a plugin-system.
  - add support for features like special file support, persistence, and real-time collab through plugins



## CONVENTIONS
Maps have names of the form `key_to_value`  
Arrays have names of the form `value_by_key`

avoid global mutable state (apart from initialization) to facilitate async programming


## DESIGN ASSUMPTIONS, PERFORMANCE TECHNIQUES

### General Strategy
most optimization effort was spent on the code that runs frequently.  
the lexer initialization code was written for maintainability and debuggability, hence why it uses Map<String, _> instead of Array  
two major areas:
  lookups
  minimize object creation
    don't build the same string multiple times
    use slices where applicable

### JS builtins' implementations
formed according to various dev blogs, API docs or benchmarks taken on my machine (Firefox)

- TypedArrays are at least as optimized as arrays of ints

- Maps are on par with regular objects for variable keys or one-off instances
  - according to V8 blog, using Map for one-off instance reduces the burden on the engine (fewer unique objects -> fewer hidden classes to maintain)

- String::substring() does not perform a copy, instead references the original string
  - no measured difference for slice() vs substring() for lexemes.

- array.join('') is on par with string +=

- simple functions are inlined

- let does not pose a significant performance impact when not captured by a closure

- Math.imul is potentially more performant than regular '*'. On Firefox, did not measure a slowdown.


### Data quantities
~10 questions
~80 students
<100KB file per student
~8 MB total.
benchmark primarily against 1MB file

<10 equivalence classes per problem
Highly clustered semantic equivalence classes

Most submissions use function names very close to those in the assignment


### lexer generator

assume <255 states in DFA
1 byte per entry in jumptable
only handle ASCII - 128 entries per state
128 bytes per state.
255 * 128 Bytes =~ 32KB
that's nothing!

actually ~70 states. -> ~9KB. ripe for L1/L2 cache!

### UTF8/16 handling
Racket supports Unicode. Presumably JS converts this to UTF16 when uploading the file.  
This is a challenge for the char-indexed lookup tables, as we can't afford to have tables with thousands or millions of cells.  
We want all chars to have codepoints between 0 and 127, to allow efficient table lookups,
and so that the JS engine has a reasonable chance of optimizing a switch-statement into a jump-table.

#### key insight
codepoints are only used to decide the token type. the actual slice comes from the input string.  
so, char -> codepoint mapping merely needs to be precise enough to correctly categorize characters.  
so, for a set of chars C, if every state transition involving chars in C is consistent (all chars in C produce same state),  
we can map them to the same codepoint before doing the state table lookup.  
For efficiency, we want to be able to recognize chars in C with as little work as possible.  
For this, I propose using the first few ASCII control characters, which can be recognized with `charcode < 5`.  
Now, we have a few 'free codepoints' with which to remap the pesky non-ascii chars.  

#### remapping non-ascii (codepoint >= 128)
JS strings are UTF16 (at least observably) - 2bytes or 4bytes per char.
We want to distinguish the characters that span 4bytes from the others, as we will need to advance the token index again.
Thus we will have a codepoint for unicode1 and unicode2, and the lexer will check if it got unicode2 and if so, advance the char index twice.

same principle works for utf8

### avoiding full parsing
although having the AST would be nice,
it's too much work without just importing a library.
Can instead start collecting at every top-level open paren
if no closing paren, abort.
and discard those that don't have define as 2nd slice

### duplicate code matching
most code will have common prefixes
hashing is too expensive, too much redundant work.
the token IDs are not sufficieent - ID especially.

could create map from ID to int.
strings, symbols almost never appear anyway.


so, use sequence of token str slices as key
store in trie
each node is a map from
str -> sub-trie
    |
SYM -> set(top_level_def_names)

#### usage
trie per file

build from lexeme seqs of each top-level definition
so: if you search the trie with a subseq of definition D,
you should get back a set including D

#### building process
##### basic
given (seq of n strs 'seq', value to associate 'assoc')
start at root node

node = root
for i from 1 to n:
  if node has seq[i]:
    node = node[seq[i]]
  else:
    break and create rest of tries

if node has [ACC KEY]: add value to set
else create new set, and entry

##### with subseqs
stack of ___ idx or node?
when you see a open delim, add root to stack
when you see a closing delim, pop last node from stack and add to ACC_KEY
otherwise, push slice to each node in stack

#### more efficient group matching
can do same thing with groups' patterns
make trie from all groups, with leaf set being group names

#### matching tries against tries
ideally, trie node would be sorted (array or tree)
then can traverse intersection faster

init result_array []
nodes a, b start at roots
get intersection of entries (for k in a where k in b)
for key k in intersection:
  if k == LEAF_NODE_KEY:
    a[k] or b[k] has the goods.
  match(a[k], b[k], result_array)
