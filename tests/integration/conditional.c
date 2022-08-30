// Test conditional operator.
int main()
{
    __clauf_assert((1 ? 11 : 42) == 11);
    __clauf_assert((0 ? 11 : 42) == 42);
}
