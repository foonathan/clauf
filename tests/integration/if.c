int if_with_else(int condition)
{
    if (condition)
        return 1;
    else
        return 2;
}

int if_without_else(int condition)
{
    if (condition)
        return 1;

    return 2;
}

int if_with_else_if(int condition)
{
    if (condition == 0)
        return 0;
    else if (condition == 1)
        return 1;
    else
        return 2;
}

int main()
{
    __clauf_assert(if_with_else(0) == 2);
    __clauf_assert(if_with_else(1) == 1);

    __clauf_assert(if_without_else(0) == 2);
    __clauf_assert(if_without_else(1) == 1);

    __clauf_assert(if_with_else_if(0) == 0);
    __clauf_assert(if_with_else_if(1) == 1);
    __clauf_assert(if_with_else_if(2) == 2);
    __clauf_assert(if_with_else_if(3) == 2);
}
