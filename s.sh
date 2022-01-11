#!/bin/bash
#SBATCH --job-name=Anjiang_QF_IDL_BENCH
#SBATCH --time=00:10:00
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem-per-cpu=4G
#SBATCH --output=/home/users/sotoudeh/batch_data/%j_%a.log
#SBATCH --error=/home/users/sotoudeh/batch_data/%j_%a.err
#SBATCH --array 1-500%100

# We have 2372 things (excluding the LFS ones), we want to have 500 tasks
# total. So we need to do 5 per task.

SLURM_ARRAY_TASK_ID=$((SLURM_ARRAY_TASK_ID - 1))
beginl=$((SLURM_ARRAY_TASK_ID * 5))
beginl=$((beginl + 1))
endl=$((beginl + 4)) # inclusive
files=$(sed -n "${beginl},${endl}p" file_list)
# https://stackoverflow.com/questions/24628076/convert-multiline-string-to-array
IFS=$'\n'
files=($files)
IFS=$' '
for i in {0..4}; # inclusive
do
    file=${files[i]}
    if [ ! -n $file ] ; then
        echo "Too many"
        exit 0
    fi
    echo "Running against file: $file"
    time timeout 2m build/bin/cvc5 --arith-idl-ext $file
done
