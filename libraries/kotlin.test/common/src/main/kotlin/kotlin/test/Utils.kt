package kotlin.test

internal fun messagePrefix(message: String?) = if (message == null) "" else "$message. "
internal header fun lookupAsserter(): Asserter

@PublishedApi // TODO: required until internal available in tests
internal fun overrideAsserter(value: Asserter?): Asserter? {
    // TODO: incorrect js generated: return _asserter.also { _asserter = value }
    val previous = _asserter
    _asserter = value
    return previous
}