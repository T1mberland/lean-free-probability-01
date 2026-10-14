# Repository Instructions

## 10. Git Workflow and Repository Management

You are responsible for maintaining a clean, well-organized Git repository throughout development.

**Use Git actively and autonomously. Do not treat version control as an afterthought.**

### Branching strategy

- Keep `main` as the stable integration branch.
- Create appropriately named feature branches for independent units of work, e.g. `feat/algebraic-foundations`, `feat/free-independence`, `feat/noncrossing-partitions`, `feat/analytic-transforms`, `feat/fock-semicircular`.
- Use `fix/`, `refactor/`, and `docs/` prefixes when appropriate.
- Branch from the latest stable main unless there is a justified dependency between branches.
- Avoid making substantial experimental changes directly on `main`.
- Keep branches focused and reasonably short-lived.

### Commits

Make regular, meaningful, atomic commits as development progresses.

- Commit completed definitions, lemmas, refactorings, documentation, and verified milestones separately when appropriate.
- Use descriptive commit messages, preferably following Conventional Commits.
- Review `git diff` and `git status` before committing.
- Stage only files related to the intended change.
- Never accidentally commit build artifacts, temporary files, credentials, or unrelated changes.
- Preserve a working, compilable state whenever practical.
- Do not mix unrelated mathematical developments into a single large commit.

Example messages:

- `feat(algebraic): define noncommutative probability spaces`
- `feat(freeness): prove mixed second-moment factorization`
- `feat(combinatorics): formalize noncrossing partitions`
- `feat(rmt): establish rank-one no-outlier criterion`
- `fix(analytic): correct assumptions in resolvent lemma`
- `docs: update formalization dependency graph`

### Verification before merging

Before merging a feature branch:

1. Ensure all completed modules compile successfully.
2. Run relevant tests and `lake build`.
3. Audit important theorems using `#print axioms`.
4. Check for `sorry`, `admit`, unintended axioms, and kernel-bypass mechanisms.
5. Review the diff for unintended changes and mathematical inconsistencies.
6. Ensure existing formalized results remain valid.

Do not merge broken, unverified, or mathematically incomplete work into `main`.

Incomplete experimental work may remain on a clearly labeled development branch.

### Merging and pushing

When a feature is complete and verified:

1. Commit the final changes on its feature branch.
2. Fetch remote changes and check whether the target branch has advanced.
3. Resolve any integration conflicts carefully.
4. Merge into `main`, using a pull request where available and appropriate.
5. Run the integration build and tests.
6. Push the updated `main` to the configured remote repository.

Push every new commit to the configured remote immediately after committing.
The user oversees development primarily through GitHub commits, so do not wait
for another milestone, the end of a session, or a merge to publish a commit.
This applies to documentation, fixes, refactorings, and clearly labeled
experimental commits as well as verified mathematical milestones. Incomplete
work must stay on a development branch; the verification requirements for
merging into `main` still apply.

Publish a new branch with its first commit using
`git push --set-upstream <remote> <branch>`, then push after every subsequent
commit. Push the feature branch before merging and push `main` after verified
integration, so GitHub shows both the development and integration history.
Do not accumulate unpublished local commits. Confirm each push succeeded before
continuing development; if it fails, preserve the local commit and report the
blocker immediately.
Report any commit or push blocker immediately; use an authorized GitHub connector
when available, and record remote commit hashes if local Git metadata cannot be
updated. Publish commits and branches even while the broader research goal is
paused when the user explicitly requests repository synchronization.

You are authorized to create branches, commit, merge, and push development changes to the configured repository, subject to repository permissions and branch protection rules.

Do not force-push, rewrite shared history, bypass branch protections, or delete someone else's work. Do not overwrite pre-existing uncommitted changes. If no usable remote or push permission is configured, preserve local commits and report the blocker rather than inventing credentials or remote URLs.

### Parallel agent development

If multiple agents work concurrently:

- Prefer separate Git worktrees and dedicated branches for each agent.
- Assign non-overlapping files or modules whenever possible.
- Coordinate shared interfaces before implementing dependent features.
- Integrate changes sequentially after review and verification.
- Do not allow multiple agents to modify the same working tree unsafely.

### Progress and history

Maintain a clean, traceable development history.

At major milestones, report:

- Current branch and commit hash.
- Newly completed mathematical results.
- Verification and build status.
- Branches merged into `main`.
- Push status and remote branch.
- Remaining incomplete branches and their blockers.

Use Git history as a reliable record of mathematical progress, not merely a backup mechanism.

**Overall principle:** develop on focused feature branches, make meaningful commits, verify mathematical correctness, merge stable results into `main`, and push regularly. Handle this workflow autonomously without requiring user approval for routine Git operations.
