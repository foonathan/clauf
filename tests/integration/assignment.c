// Test assignment operators.
int main()
{
    int i;
    __clauf_assert((i = 0) == 0);
    __clauf_assert((i = 11) == 11);

    __clauf_assert((i += 2) == 13);
    __clauf_assert((i -= 6) == 7);

    int j;
    __clauf_assert((i = j = 1) == 1);
    __clauf_assert i == 1;
    __clauf_assert j == 1;
}
