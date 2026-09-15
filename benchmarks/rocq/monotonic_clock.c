#define _POSIX_C_SOURCE 200809L

#include <stdint.h>
#include <time.h>

#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/mlvalues.h>

/*
 * OCaml 4.13 does not expose clock_gettime through Unix.  Keeping this binding
 * beside the extracted Flocq driver gives every supported OCaml version the
 * same monotonic timer instead of quietly falling back to wall-clock time.
 */
CAMLprim value floatlib_monotonic_nanos(value unit) {
  (void)unit;
  struct timespec now;
  if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) {
    caml_failwith("clock_gettime(CLOCK_MONOTONIC) failed");
  }
  int64_t nanos =
      (int64_t)now.tv_sec * INT64_C(1000000000) + (int64_t)now.tv_nsec;
  return caml_copy_int64(nanos);
}
