// RLIBM defines these functions in C++, while the comparison reporter loads
// providers through C's stable symbol names. Keep the boundary explicit here
// instead of relying on compiler-specific C++ name mangling.

float rlibm_exp(float);
float rlibm_log(float);
float rlibm_sinh(float);
float rlibm_cosh(float);

extern "C" float floatlib_rlibm_exp(float value) {
  return rlibm_exp(value);
}

extern "C" float floatlib_rlibm_log(float value) {
  return rlibm_log(value);
}

extern "C" float floatlib_rlibm_sinh(float value) {
  return rlibm_sinh(value);
}

extern "C" float floatlib_rlibm_cosh(float value) {
  return rlibm_cosh(value);
}
