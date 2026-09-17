/*
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
*/
#pragma once
#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

LEAN_EXPORT lean_obj_res lean_byte_array_push16(lean_obj_arg a, uint16_t v);
LEAN_EXPORT lean_obj_res lean_byte_array_push32(lean_obj_arg a, uint32_t v);
LEAN_EXPORT lean_obj_res lean_byte_array_push64(lean_obj_arg a, uint64_t v);

#ifdef __cplusplus
}
#endif
