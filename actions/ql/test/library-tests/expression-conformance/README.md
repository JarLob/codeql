# GitHub Actions expression syntax conformance

These tests cover the syntax-only layer of the public GitHub Actions expression parser at
[`actions/runner@de4c2885af3311c1ed2f24b9e86617ed51d7a6bf`](https://github.com/actions/runner/tree/de4c2885af3311c1ed2f24b9e86617ed51d7a6bf).

The vectors are derived from the public parser, lexer, constants, precedence table, and L0 parser
tests. They do not include or copy the private `actions-expressions` shared corpus.

This suite checks:

- accepted and rejected lexical/syntactic forms;
- operator precedence and associativity through a canonical binary tree representation;
- function, property, index, and wildcard structure;
- the public maximum expression depth of 50.

It intentionally does not check registered context names, evaluation results, or exact runner node
classes. The QL parser is used as a syntax parser, equivalent to the runner's `ValidateSyntax`
mode; syntax validation still checks the arity of public well-known functions. Associative runner
nodes are represented canonically as binary trees. The public maximum length of 21,000 characters
is generated and checked in the QL test rather than materialized as a 21 KB workflow fixture.
