## Description

Proofs in Coq written during groupe de travail at ENS on formal methods.

## How to use github?

Repository is cloned with
```
git clone https://github.com/ENS-formal-math/coq-gt.git
```

This will clone the repository onto your local machine and you can begin working. The best pipeline is the following:

1. You start working and before doing anything, pull recent changes done by other collaborators
```
git pull
```
2. You do some local changes which serve one logical purpose. For instance, you have written one new file. 
3. You check what has been changed using
```
git status
```
4. You add all changed/created files as
```
git add <file>
```
or delete (be careful) moved/deleted files with
```
git rm <file>
```
5. You gather changes and commit them under some name, which should explain what has be done (like "add ring.v")
```
git commit -m <commit-name>
```
6. If you want, you can repeat steps 1-4 several times and do several commits, since after you have committed you are much more safer at not accidentaly discarding your progress. Otherwise, you proceed immediately to the step of pushing you results to the shared repository
```
git push
```
**Attention!** It may happen so that someone has pushed new changes while you were working. In that case you have to do
```
git pull
```
There may be merge conflicts that will have to be resolved. For instance if you and your collaborator were working on the same file and did different things, you will get a glued version of two files. You will have to choose an appropriate version and rewrite the file. After resolving the conflicts locally, you will have to commit a resolution. Then you will be able to push this commit and previous ones. Clearer instruction may be found [here](https://opensource.com/article/23/4/resolve-git-merge-conflicts).


## How to generate Coq projects

If you have several Coq files in your project, which need to import one each other, you have to compile them. One can do it manually with ```coqc``` command, but as project grows it becomes inefficient. 

One uses tool ```coq_makefile```. First one defines project structure in text file _CoqProject (notice that it has no extension like .txt). For simple one-folder project, one can use following template
```
-R <dir> <package-name>

<dir>/<file-1>
<dir>/<file-2>
...
```
Here we have defined that our files lie in a directory ```<dir>``` and bound our project to a ```<package-name>```. Then one should be able to import files in Coq with ```Require Import <package-name>.<file>```. More on import commands can be found [here](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#).

Finally, in order for project to work, we need to compile it with
```
coq_makefile -f _CoqProject -o Makefile
make
```