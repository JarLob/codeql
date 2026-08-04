/**
 * Provides matching for the glob syntax used by GitHub Actions trigger filters.
 *
 * This models the glob matching behavior used for GitHub Actions trigger filters. In particular,
 * `?` and `+` are postfix quantifiers, `*` does not match `/`, and `**` does match `/`.
 */

/** Holds if `pattern` is a negative pattern in a glob sequence. */
bindingset[pattern]
pragma[inline_late]
predicate isNegative(string pattern) { pattern.charAt(0) = "!" }

bindingset[pattern]
pragma[inline_late]
private string getPatternBody(string pattern) {
  if isNegative(pattern) then result = pattern.substring(1, pattern.length()) else result = pattern
}

bindingset[literal]
pragma[inline_late]
private string quoteRegexpLiteral(string literal) {
  if literal = ["\\", ".", "+", "*", "?", "(", ")", "|", "[", "]", "{", "}", "^", "$"]
  then result = "\\" + literal
  else result = literal
}

bindingset[character]
pragma[inline_late]
private int getAsciiRangeIndex(string character) {
  result = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".indexOf(character)
}

bindingset[pattern, start]
pragma[inline_late]
private int getRangeEnd(string pattern, int start) {
  result =
    min(int index |
      index in [start + 1 .. pattern.length() - 1] and
      pattern.charAt(index) = "]"
    |
      index
    )
}

private string getRangeTokenRegexp() {
  result = "\\[(?:\\^)?(?:[0-9](?:-[0-9])?|[A-Za-z](?:-[A-Za-z])?)+\\]"
}

private string getQuantifiableTokenRegexp() {
  result = "(?:\\\\[\\s\\S]|" + getRangeTokenRegexp() + "|[^\\\\*?+\\[])"
}

private string getTokenSequenceRegexp() {
  result = "(?:" + getQuantifiableTokenRegexp() + "[?+]?|\\*\\*/?|\\*)*"
}

bindingset[pattern, index]
pragma[inline_late]
private predicate isTokenBoundary(string pattern, int index) {
  index in [0 .. pattern.length()] and
  pattern.substring(0, index).regexpMatch(getTokenSequenceRegexp())
}

bindingset[pattern, index]
pragma[inline_late]
private int getNextTokenBoundary(string pattern, int index) {
  result =
    min(int next | next in [index + 1 .. pattern.length()] and isTokenBoundary(pattern, next) | next)
}

bindingset[pattern, index]
pragma[inline_late]
private predicate isConsumedByDoubleStar(string pattern, int index) {
  index > 0 and
  pattern.substring(index - 1, index + 1) = "**" and
  isTokenBoundary(pattern, index - 1)
  or
  index > 1 and
  pattern.charAt(index) = "/" and
  pattern.substring(index - 2, index) = "**" and
  isTokenBoundary(pattern, index - 2)
}

bindingset[pattern]
pragma[inline_late]
private predicate hasReversedRange(string pattern) {
  exists(int start, int rangeEnd, string content, int index |
    isTokenBoundary(pattern, start) and
    pattern.charAt(start) = "[" and
    rangeEnd = getRangeEnd(pattern, start) and
    content = pattern.substring(start + 1, rangeEnd) and
    content.charAt(index) = "-" and
    getAsciiRangeIndex(content.charAt(index - 1)) > getAsciiRangeIndex(content.charAt(index + 1))
  )
}

bindingset[pattern]
pragma[inline_late]
private predicate hasTooManyStars(string pattern) {
  exists(int index |
    index in [0 .. pattern.length() - 3] and
    isTokenBoundary(pattern, index) and
    pattern.substring(index, index + 3) = "***"
  )
}

/** Holds if `pattern` is accepted by the Actions trigger glob parser. */
bindingset[pattern]
pragma[inline_late]
predicate isValid(string pattern) {
  getPatternBody(pattern).regexpMatch(getTokenSequenceRegexp()) and
  not hasReversedRange(getPatternBody(pattern)) and
  not hasTooManyStars(getPatternBody(pattern))
}

bindingset[pattern, index]
pragma[inline_late]
private string getRegexpFragment(string pattern, int index) {
  isTokenBoundary(pattern, index) and
  not isConsumedByDoubleStar(pattern, index) and
  (
    pattern.charAt(index) = "\\" and
    result = "\\" + pattern.charAt(index + 1)
  )
  or
  isTokenBoundary(pattern, index) and
  not isConsumedByDoubleStar(pattern, index) and
  pattern.substring(index, index + 2) = "**" and
  result = ".*"
  or
  isTokenBoundary(pattern, index) and
  not isConsumedByDoubleStar(pattern, index) and
  pattern.charAt(index) = "*" and
  not pattern.charAt(index + 1) = "*" and
  result = "[^/]*"
  or
  isTokenBoundary(pattern, index) and
  not isConsumedByDoubleStar(pattern, index) and
  pattern.charAt(index) = ["?", "+"] and
  result = pattern.charAt(index)
  or
  isTokenBoundary(pattern, index) and
  not isConsumedByDoubleStar(pattern, index) and
  pattern.charAt(index) = "[" and
  exists(int rangeEnd, string content |
    rangeEnd = getRangeEnd(pattern, index) and
    content = pattern.substring(index + 1, rangeEnd) and
    result = "[" + content + "]"
  )
  or
  isTokenBoundary(pattern, index) and
  not isConsumedByDoubleStar(pattern, index) and
  not pattern.charAt(index) = ["\\", "*", "?", "+", "["] and
  result = quoteRegexpLiteral(pattern.substring(index, getNextTokenBoundary(pattern, index)))
}

bindingset[pattern]
pragma[inline_late]
private string getRegexp(string pattern) {
  isValid(pattern) and
  result =
    "^" +
      concat(int index |
        index in [0 .. getPatternBody(pattern).length() - 1]
      |
        getRegexpFragment(getPatternBody(pattern), index), "" order by index
      ) + "$"
}

/** Holds if `pattern`, ignoring sequence negation, matches all of `input`. */
bindingset[pattern, input]
pragma[inline_late]
predicate patternMatches(string pattern, string input) {
  isValid(pattern) and input.regexpMatch(getRegexp(pattern))
}
