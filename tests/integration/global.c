int global;
const int global_const = 2 * 20 + 2;

int main()
{
    static int fn_static = 11;

    __clauf_assert(global == 0);
    __clauf_assert(global_const == 42);
    __clauf_assert(fn_static == 11);

    global = fn_static;
    ++fn_static;

    __clauf_assert(global == 11);
    __clauf_assert(fn_static == 12);

    int global = 9; // shadow
    __clauf_assert(global == 9);
}

