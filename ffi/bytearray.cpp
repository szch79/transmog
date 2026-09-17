/*
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
*/
#include "bytearray.h"

extern "C" lean_obj_res lean_sarray_ensure_capacity(lean_obj_arg a,
                                                    size_t min_cap, bool exact);

namespace {
template <typename T> void write_le(lean_object *a, size_t i, T value) {
  for (size_t j = 0; j < sizeof(T); ++j)
    lean_sarray_cptr(a)[i + j] = static_cast<uint8_t>(value >> (8 * j));
}
} // namespace

extern "C" LEAN_EXPORT lean_obj_res lean_byte_array_push16(lean_obj_arg a,
                                                           uint16_t v) {
  const size_t size = lean_sarray_size(a);
  lean_obj_res r = lean_sarray_ensure_exclusive(
      lean_sarray_ensure_capacity(a, size + 2, false));
  write_le(r, size, v);
  lean_sarray_set_size(r, size + 2);
  return r;
}

extern "C" LEAN_EXPORT lean_obj_res lean_byte_array_push32(lean_obj_arg a,
                                                           uint32_t v) {
  const size_t size = lean_sarray_size(a);
  lean_obj_res r = lean_sarray_ensure_exclusive(
      lean_sarray_ensure_capacity(a, size + 4, false));
  write_le(r, size, v);
  lean_sarray_set_size(r, size + 4);
  return r;
}

extern "C" LEAN_EXPORT lean_obj_res lean_byte_array_push64(lean_obj_arg a,
                                                           uint64_t v) {
  const size_t size = lean_sarray_size(a);
  lean_obj_res r = lean_sarray_ensure_exclusive(
      lean_sarray_ensure_capacity(a, size + 8, false));
  write_le(r, size, v);
  lean_sarray_set_size(r, size + 8);
  return r;
}
