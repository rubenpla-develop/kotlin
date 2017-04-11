class Predicate(val x: Boolean) {
    operator fun invoke() = x

    operator fun not() = Predicate(-x)
}

fun test(p: Predicate) {
    val x = -p
    println(<caret>x())
}