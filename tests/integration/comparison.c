// Test comparison operators.
int main()
{
    __clauf_assert(11 > 5);
    __clauf_assert(11 >= 5);
    __clauf_assert(!(11 < 5));
    __clauf_assert(!(11 <= 5));
    __clauf_assert(!(11 == 5));
    __clauf_assert(11 != 5);

    __clauf_assert(3 > -3);
    __clauf_assert(3 >= -3);
    __clauf_assert(!(3 < -3));
    __clauf_assert(!(3 <= -3));
    __clauf_assert(!(3 == -3));
    __clauf_assert(3 != -3);
}
