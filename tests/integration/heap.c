void* malloc(unsigned int size)
{
    return __clauf_malloc(size);
}

void free(void* ptr)
{
    if (ptr != nullptr)
        __clauf_free(ptr);
}

int main()
{
    int* ptr = malloc(sizeof(int));

    *ptr = 0;
    __clauf_assert(*ptr == 0);

    *ptr = 11;
    __clauf_assert(*ptr == 11);

    free(ptr);
    free(nullptr);
}

