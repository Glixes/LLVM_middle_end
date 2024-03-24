# Note
Dopo aver pullato il branch DEV mediante
     git pull origin DEV

git crea un branch DEV nel quale ha pullato i cambiamenti effettuati sul branch. è possibile successivamente modificarlo e poi eseguire i seguenti comandi

    git checkout main
    git merge DEV

per eseguire il merge dei branch.

NOTA: questo non comporta che il branch venga eliminato nè localmente nè tantomento sul repository (vd. github). Per eliminarlo localmente

      git branch -d <nome_branch>

L'opzione -d è migliore rispetto -D in quanto controlla che prima sia stato eseguito il merge. 



