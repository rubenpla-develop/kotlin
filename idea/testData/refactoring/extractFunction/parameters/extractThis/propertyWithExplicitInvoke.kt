// PARAM_DESCRIPTOR: public final class A defined in root package
// PARAM_TYPES: A
// SIBLING:
class A {
    val foo: () -> String = { "OK" }
    fun bar() = <selection>foo.invoke()</selection>
}