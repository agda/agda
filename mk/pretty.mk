MSG_WIDTH=70

define decorate
TITLE=$(strip $1);\
LABEL=$@;\
TITLE_LEN=$$(( $${#TITLE} + 2));\
LEFT_PAD=$$(( (${MSG_WIDTH} - $${TITLE_LEN}) / 2));\
RIGHT_PAD=$$(( $${LEFT_PAD} + $${TITLE_LEN} % 2 ));\
if [ "${TRAVIS}" = "true" ]; then\
  echo -e "travis_fold:start:$${LABEL}";\
	echo -e "\033[1m\033[33m$${TITLE}\033[0m";\
else\
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
fi   ;\
$(2) &&\
if [ "${TRAVIS}" = "true" ]; then                     \
  echo -e "travis_fold:end:$${LABEL}";       \
fi
endef
