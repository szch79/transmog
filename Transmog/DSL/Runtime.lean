/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Transmog.DSL.Runtime.Basic
public meta import Transmog.DSL.Runtime.Pass
public meta import Transmog.DSL.Runtime.Retag

/-!
# Word-backed runtime representation support

Importing this module installs the code generator passes, so every module that can compile code
touching a word-backed type must reach it through a `public meta import` chain.
-/
