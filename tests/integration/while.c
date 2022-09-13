int simple_while(int n)
{
    int result;
    result = 0;
    while (n > 0)
    {
        result += 1;
        n -= 1;
    }
    return result;
}

int simple_do_while(int n)
{
    int result;
    result = 0;
    do
    {
        result += 1;
        n -= 1;
    } while (n > 0);
    return result;
}

int while_break(int n)
{
    int result;
    result = 0;
    while (n > 0)
    {
        if (n == 5)
            break;
        result += 1;
        n -= 1;
    }
    return result;
}

int while_continue(int n)
{
    int result;
    result = 0;
    while (n > 0)
    {
        if (n == 5)
        {
            n -= 1;
            continue;
        }
        result += 1;
        n -= 1;
    }
    return result;
}

int main()
{
    __clauf_assert simple_while(-1) == 0;
    __clauf_assert simple_while(0) == 0;
    __clauf_assert simple_while(2) == 2;
    __clauf_assert simple_while(10) == 10;

    __clauf_assert simple_do_while(-1) == 1;
    __clauf_assert simple_do_while(0) == 1;
    __clauf_assert simple_do_while(2) == 2;
    __clauf_assert simple_do_while(10) == 10;

    __clauf_assert while_break(-1) == 0;
    __clauf_assert while_break(0) == 0;
    __clauf_assert while_break(2) == 2;
    __clauf_assert while_break(10) == 5;

    __clauf_assert while_continue(-1) == 0;
    __clauf_assert while_continue(0) == 0;
    __clauf_assert while_continue(2) == 2;
    __clauf_assert while_continue(10) == 9;
}

