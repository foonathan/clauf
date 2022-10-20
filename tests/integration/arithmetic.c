// Test arithmetic expressions.
int main()
{
    __clauf_assert(1 + 2 == 3);
    __clauf_assert(1 - 2 == -1);
    __clauf_assert(2 * 3 == 6);
    __clauf_assert(10 / 3 == 3);
    __clauf_assert(10 % 3 == 1);

    __clauf_assert((0b101 & 0b110) == 0b100);
    __clauf_assert((0b101 | 0b110) == 0b111);
    __clauf_assert((0b101 ^ 0b110) == 0b011);
    __clauf_assert((0b101 << 2) == 0b10100);
    __clauf_assert((0b101 >> 2) == 0b1);

    __clauf_assert(+1 == 1);
    __clauf_assert(~(-1) == 0);
    __clauf_assert(!0 == 1);
    __clauf_assert(!1 == 0);
}
