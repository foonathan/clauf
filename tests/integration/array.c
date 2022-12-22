int foo(int array[])
{
    array[0] = 42;
    return array[1];
}

int main()
{
    {
        int array[3] = {1, 2};
        __clauf_assert(sizeof(array) == 3 * sizeof(int));
        __clauf_assert(alignof(int[3]) == alignof(int));

        __clauf_assert(array[0] == 1);
        __clauf_assert(array[1] == 2);
        __clauf_assert(array[2] == 0);

        array[2] = 3;
        __clauf_assert(array[2] == 3);

        *array = 11;
        __clauf_assert(array[0] == 11);

        __clauf_assert(foo(array) == 2);
        __clauf_assert(array[0] == 42);
    }
    {
        int a       = 42;
        int array[] = {42};
        __clauf_assert(array[0] == 42);
    }
    {
        int array[3][2];

        array[0][0] = 1;
        array[0][1] = 2;
        array[1][0] = 3;
        array[1][1] = 4;
        array[2][0] = 5;
        array[2][1] = 6;

        int* ptr = &array[0][0];
        __clauf_assert(ptr[0] == 1);
        __clauf_assert(ptr[1] == 2);
        __clauf_assert(ptr[2] == 3);
        __clauf_assert(ptr[3] == 4);
        __clauf_assert(ptr[4] == 5);
        __clauf_assert(ptr[5] == 6);
    }
}
