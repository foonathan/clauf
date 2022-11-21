extern void* a;
extern void* b;

void f();
void g();

void* a = &b;
void* b = &a;

void f()
{
    g();
}

void g()
{
    f();
}

int main() {}

