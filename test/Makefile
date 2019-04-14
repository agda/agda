
## Lines of Code ##########################################################

locfiles=$(shell find . \( \( -name '*agda.*' -o -name '*agda' -o -name '*.in' -o -name '*hs' \) ! -name '.*' \) -not \( -path "*/MAlonzo/*" -o -path "./bugs/*" -o -path "./bugs-lib/*" -o -path "./features/*" \) | sort)

loc :
	@wc $(locfiles)

debug_loc :
	@echo "locfiles=$(locfiles)"

# EOF
