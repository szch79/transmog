import Lake
open Lake DSL

package transmogConsumer

require transmog from "../.."

lean_lib Support where
  roots := #[`Consume, `Relay]

@[default_target]
lean_exe consumer where
  root := `Main
