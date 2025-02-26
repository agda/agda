MSG_WIDTH=70

define decorate
TITLE=$(strip $1);\
LABEL=$@;\
TITLE_LEN=$$(( $${#TITLE} + 2));\
LEFT_PAD=$$(( (${MSG_WIDTH} - $${TITLE_LEN}) / 2));\
RIGHT_PAD=$$(( $${LEFT_PAD} + $${TITLE_LEN} % 2 ));\
	printf '=%.0s' {1..${MSG_WIDTH}};\
	printf "\n";\
  for ((i=1; i<= $${LEFT_PAD}; i++)); do\
	  printf "=";\
	done;\
	printf " $${TITLE} ";\
  for ((i=1; i<= $${RIGHT_PAD}; i++)); do\
	  printf "=";\
	done;\
	printf "\n";\
	printf '=%.0s' {1..${MSG_WIDTH}};\
	printf "\n";\
$(2)
endef
