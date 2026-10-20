"""Compatibility entry point for the runtime-bound schema-3 verifier.

The round-6 implementation is preserved in the Git review snapshot.
"""
from verify_integrated import *  # re-export the current verifier API

if __name__ == "__main__":
    main()
