#include <stdio.h>
#include <stdlib.h>
#include "values.h"
#include "print.h"
#include "runtime.h"

FILE* in;
FILE* out;
void (*error_handler)();
val_t *heap;

void error_exit()
{
  printf("err\n");
  exit(1);
}

void raise_error()
{
  return error_handler();
}

int main(int argc, char** argv)
{
  in = stdin;
  out = stdout;
  error_handler = &error_exit;
  heap = malloc(8 * heap_size);
  
  val_vect_t result;
 
  *result = entry(heap);
  for (int i = 0; i < result->len; ++i) {
    print_result(result->elems[i]);
    if (val_typeof(result->elems[i]) != T_VOID)
      putchar('\n');
  }


  free(heap);
  return 0;
}
