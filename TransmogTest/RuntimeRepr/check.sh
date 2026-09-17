#!/bin/sh
# Assertions on the C that the code generator emits for the word-backed probes.  `lake test`
# runs this after building the test modules; run it by hand from the repository root.
#
# At non-inlined boundaries a word-backed value still has Lean's object ABI, not the scalar ABI
# of its carrier.  On a 64-bit host boxing a `UInt32` produces an immediate rather than a heap
# object; these checks establish nothing about 32-bit targets.
set -eu

lake build TransmogTest

# Check that the exported probes and the derived comparison workers of one generated C file
# reach the word-backed values without ever touching the object layout.  `expected` guards
# against the pattern silently matching nothing after a rename.  For the reclassified types,
# whose probes and workers are recognised by name, any reference counting operation is rejected
# as well; that is what the IR classification override buys.
scan() {
  awk -v file="$1" -v expected="$2" '
    /^LEAN_EXPORT .*\)\{/ {
      probe = $0 ~ /^LEAN_EXPORT .* runtime_[a-z_0-9]+\(/
      worker = $0 ~ /^LEAN_EXPORT .*inst(BEq|DecidableEq|Hashable|Ord)(Node|Cell|Op|Signed|Edge)_[a-zA-Z]+\(/
      checking = probe || worker
      rc = $0 ~ /runtime_(signed|edge)_[a-z_0-9]+\(/ || $0 ~ /inst(BEq|DecidableEq)(Signed|Edge)_/
      if (checking) { count++; name = $0 }
    }
    /^(LEAN_EXPORT )?lean_object\* [a-z_]*initialize_/ { checking = 0 }
    checking && /lean_obj_tag|lean_ctor_get|lean_alloc_ctor|lean_alloc_closure|lean_apply_[0-9]/ {
      print "Unexpected constructor access, allocation, or indirect call in " name ":\n" $0
      failed = 1
    }
    checking && rc && /lean_(inc|dec)(_ref|_n|_ref_n)?\(/ {
      print "Unexpected reference counting in " name ":\n" $0
      failed = 1
    }
    END {
      if (count != expected) {
        print "Expected " expected " checked functions in " file ", found " count
        failed = 1
      }
      if (failed) exit 1
      print file ": no constructor access, aggregate allocation, or indirect calls, and no reference counting on the reclassified types."
    }
  ' "$1"
}

scan .lake/build/ir/TransmogTest/RuntimeRepr/Probes.c 45
scan .lake/build/ir/TransmogTest/RuntimeRepr/Wide.c 6

# A constant of a word-backed type is a boxed word, not an allocated constructor.
awk '
  /^static lean_object\* _init_.*cellEmpty___boxed__const__1\(void\)\{/ { inside = 1 }
  inside && /lean_box_uint32/ { boxed = 1 }
  inside && /lean_alloc_ctor/ { allocated = 1 }
  inside && /^\}/ { inside = 0 }
  END {
    if (!boxed || allocated) {
      print "Expected the nullary constructor constant to be a boxed word"
      exit 1
    }
    print "Nullary constructor constant: boxed word."
  }
' .lake/build/ir/TransmogTest/RuntimeRepr/Probes.c

# The `Node` representation round trip compiles to the identity.
if ! grep -qE 'runtime_node_codec\(lean_object\* v_n_[0-9]+_\)\{' \
    .lake/build/ir/TransmogTest/RuntimeRepr/Probes.c; then
  echo "Expected an exported Node codec probe"
  exit 1
fi

# So does the `Edge` round trip, and a reclassified probe takes and returns `lean_object*`.
awk '
  /^LEAN_EXPORT lean_object\* runtime_edge_codec\(lean_object\* v_e_[0-9]+_\)\{/ { inside = 1; found = 1 }
  inside && /^return v_e_[0-9]+_;/ { identity = 1 }
  inside && /^\}/ { inside = 0 }
  END {
    if (!found || !identity) {
      print "Expected the Edge codec probe to compile to the identity"
      exit 1
    }
    print "Structure codec: identity."
  }
' .lake/build/ir/TransmogTest/RuntimeRepr/Probes.c

echo "Word-backed probes: no constructor access, aggregate allocation, or indirect calls."
