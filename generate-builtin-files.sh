#! /bin/sh
# generate-builtin-files.sh -- Genera el archivo BUILTIN-FILES.S

# After running this script with a list of files as argument, a file
# named BUILTIN-FILES.S will be created whose content is a primitive
# Forth word @FILENAME for each Forth file. This word leaves (in order)
# in the # data stack the following information:
#   - The address of memory where the file begins.
#   - The size of the memory buffer.
#   - The address of memory of a free location to keep information.
#     (This variable is used to store if this file was loaded
#      in the Forth image currently)

OUTPUT=BUILTIN-FILES.S

echo "/* This file was generated automatically. Don't modify it. */" > $OUTPUT
for file in $*; do
    BN=`echo $file | sed 's/\//_/g' | sed 's/\./_/g'`
    SYMBOL_START="_binary_${BN}_start"
    SYMBOL_SIZE="_binary_${BN}_size"
    echo ""                                                     >> $OUTPUT
    echo "BUILTIN_WORD_NAME(__$BN, \"@$file\")"                 >> $OUTPUT
    echo "     movl \$__${BN}_data, -4(%esi)"                   >> $OUTPUT
    echo "     subl \$4, %esi"                                  >> $OUTPUT
    echo "     ret"                                             >> $OUTPUT
    echo "__${BN}_data:"                                        >> $OUTPUT
    echo "     .long $SYMBOL_START"                             >> $OUTPUT
    echo "     .long $SYMBOL_SIZE"                              >> $OUTPUT
    echo "     .long 0"                                         >> $OUTPUT
    echo "     .long begin___$BN"                               >> $OUTPUT
    echo "END_WORD(__$BN)"                                      >> $OUTPUT
done
