int main()
{
    extern int global;
    __clauf_assert(global == 42);
}

int global = 42;

