struct foo
{
    int a;
    char b;
};

struct foo make_foo()
{
    return (struct foo){11, 'a'};
}

struct foo forward_foo(struct foo f)
{
    return f;
}

void modify_foo(struct foo* f)
{
    (*f).a = 42;
    (*f).b = 'b';
}

int main()
{
    struct foo f;

    f = forward_foo(make_foo());
    __clauf_assert(f.a == 11);
    __clauf_assert(f.b == 'a');

    modify_foo(&f);
    __clauf_assert(f.a == 42);
    __clauf_assert(f.b == 'b');
}

