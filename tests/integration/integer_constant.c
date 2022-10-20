// Test integer constants.
int main()
{
    __clauf_assert(0 == 0);

    // Decimal.
    __clauf_assert(11 == 11);
    __clauf_assert(12'3'4 == 1234);

    // Octal.
    __clauf_assert(07 == 7);
    __clauf_assert(010 == 8);
    __clauf_assert(0'20 == 16);

    // Hexadecimal.
    __clauf_assert(0x7 == 7);
    __clauf_assert(0x10 == 16);
    __clauf_assert(0XaBcD'Ef == 11259375);

    // Binary.
    __clauf_assert(0b0 == 0);
    __clauf_assert(0B11'00 == 12);
}
