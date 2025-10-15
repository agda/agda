#!/bin/sh

# Andreas, issue 8098, do not delete readonly files.

AGDA=$1

# Exit if a step fails.
set -e

# Should succeed and create Issue8098.agdai.
$AGDA Issue8098.agda

# Find interface file.
iface=$(find -name "Issue8098.agdai")
[ -f ${iface} ]

# Make interface file readonly.
chmod -w ${iface}

# Should fail, because we cannot update the interface file.
# This will print:
# Failed to write interface .../Issue8098.agdai.
# .../Issue8098.agdai:
# withBinaryFile: permission denied (Permission denied)
! $AGDA -Werror Issue8098.agda

# Make sure the file is still there.
[ -f ${iface} ]

# When Agda does not have to write the interface, it should still succeed.
$AGDA Issue8098.agda

# Remove the interface file.
chmod +w ${iface}
rm -f ${iface}

# EOF
