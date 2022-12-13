int main()
{
    int obj = 42, *ptr;

    ptr = &obj;
    __clauf_assert(*ptr == 42);

    *ptr = 11;
    __clauf_assert(*ptr == 11);
    __clauf_assert(obj == 11);

    ptr[0] = 11 + 42;
    __clauf_assert(ptr[0] == 53);
    __clauf_assert(obj == 53);
}
