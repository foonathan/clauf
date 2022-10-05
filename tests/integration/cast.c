int main()
{
    (void)42;

    unsigned       a = (unsigned)-1;
    __clauf_assert a == 0xFFFF'FFFF'FFFF'FFFF;

    int            b = (int)11u;
    __clauf_assert b == 11;
}
