module Utils.Assert

export
unreachable : a
unreachable = assert_total (idris_crash "unreachable")
