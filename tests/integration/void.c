int global;

void f()
{
    global = 42;
}

void g()
{
    global = 11;
    return;
    global = -1;
}

int main()
{
    __clauf_assert global == 0;

    f();
    __clauf_assert global == 42;

    g();
    __clauf_assert global == 11;
}

