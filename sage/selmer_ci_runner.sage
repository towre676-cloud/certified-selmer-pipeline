# No certified descent backend exists. Never copy a fixture as a computation.
raise RuntimeError('Arithmetic certificate generation unavailable: implement exact '
                   '2-descent witnesses and an independent checker first. '
                   'Legacy fixtures have not been recomputed.')
