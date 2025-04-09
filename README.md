# OKml Interpreter

This project implements an interpreter for a core fragment of OCaml called OKml (pronounced "oh-kay-mull"). This language OKml is designed so that any valid OKml program should behave the same when treated as an OCaml program.

## Workflow
Developers working on this project should adhere to the following workflow:

1. Ensure your master branch is up-to-date
```bash
git checkout master
git pull origin master
```

2. Create and switch to a new feature branch
```bash
git checkout -b your-feature-name
# Example: git checkout -b lexing
```

3. Work on your changes and make commits
- Make your code changes
- Stage the changes:
```bash
git add <files>
# or git add . to add all changes
```
- Commit with a descriptive message:
```bash
git commit -m "feat(lexing): implement Lexer for OKml"
```

4. Stay up-to-date with master while working
```bash
# First, save your current changes
git stash

# Update master
git checkout master
git pull origin master

# Return to your feature branch
git checkout your-feature-name
git merge master

# Reapply your changes
git stash pop
```

5. Push your branch to GitHub
```bash
git push origin your-feature-name
```

6. Create a Pull Request (PR)
- Follow the link shown after pushing the changes to GitHub to create a new PR

7. After PR is Approved
- New changes in the PR are now merged to the master branch.
- You can pull new changes from the remote master branch to the local master branch.
```bash
git checkout master
git pull origin master
```

8. Clean up
```bash
# Delete local branch
git branch -d your-feature-name

# Delete remote branch (optional)
git push origin --delete your-feature-name
```

## Commit types

All the commits to this repository should follow the following format:

| Type | Description |
|------|-------------|
| feat | A new feature |
| fix | A bug fix |
| docs | Documentation changes |
| style | Changes that don't affect code meaning (white-space, formatting, etc.) |
| refactor | Code changes that neither fix bugs nor add features |
| perf | Code changes that improve performance |
| test | Adding or updating tests |
| build | Changes affecting build system or external dependencies |
| ci | Changes to CI configuration files and scripts |
| chore | Other changes that don't modify src or test files |
| revert | Reverts a previous commit |
