### Project Overview

The Veri-Datalog project is a verified Datalog+ engine. It proves the
correctness of Datalog+ programs by constructing proof trees from their trace
output. Datalog+ is a research defined language that is similar to Datalog but
with more feature support; both are subsets of Prolog.

### Test Suite

In the lcf directory, running `make test` will verify the go predicate of every
Datalog+ file in the tests directory.  The results are saved as .thm files with
names matching the original code files. Using the Python script in the tools
directory, it is possible to randomly generate example Datalog+ programs
involving edge connectivity problems.

### Trace Reconstruction

The trace output of a Prolog program shows an exploration of many possible
paths before settling on one that allows the query to be true or resolves some
unification. The new trace reconstruction algorithm attempts to discard all the
failed paths and look at just the successful path, which greatly simplifies the
process of constructing a proof tree for that query. The algorithm does this by
only looking at trace events that use the exit port, since these events result
from successes and contain full variable assignments. However, failed paths can
have zero or more temporary successes, potentially leading to the presence of
"junk" events with exit ports in the trace output.

Since exit ports always follow successes, the first exit ports in the trace
happen after finding succesful base cases (builtin operations, facts, etc.),
and later exit ports show the successes of predicates that depended on other
rules and facts. As a result, the algorithm reads from the trace backwards in
order to go from the root to the leaves instead of vice versa. The algorithm
uses a mix of recursion and iteration, where the recursion helps the algorithm
move "up" and "down" the tree, and the iteration helps algorithm move between
siblings in the tree and skip junk events. A trace event with a prop such as a
fact, equality, or builtin becomes a leaf in the proof tree, whereas other
trace events become regular theorems that have proofs using other theorems and
leaves from lower down in the tree as arguments.

### Primitives and Builtins

Unlike Datalog, Datalog+ supports constants other than atoms, including
numbers, strings, and lists. These types are not complete yet. It has not been
decided yet if the numbers should be natural numbers or integers (or if both
should be supported). Furthermore, strings do not support all characters that
could be found in a legal Datalog+ string, including escaped characters such as
double quotes. Also, lists currently only support constant terms and cannot use
the pipe operator. In addition to these types, there is also support for
certain builtin operations, such as equality operators and string and list
builtins.

**Supported primitives**
* Natural numbers
* Strings
* Lists

**Supported infix operators**
* `>`
* `<`
* `=<`
* `>=`
* `\=`
* `=\=`
* `=`
* `==`

**Supported string builtin operators**
* `split_string`
* `sub_string`
* `string_lower`
* `string_chars`

**Supported list builtin operators**
* `length`
* `member`
* `reverse`
* `nth1`

### Noteable Test Cases

* `connectivity2.pl` -- Causes a choicepoint that SWIPL fails and redoes
* `connectivity4.pl` -- Causes a call, a fail, a redo, and an exit to happen consecutively at the same level
* `node1.pl` -- Requires build_proof_tree to pay attention to level
