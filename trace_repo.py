from lean_dojo import *

REPO = LeanGitRepo(
    "https://github.com/leanprover-community/NNG4",
    "e55da341a671ee4a4debcffe77efbff2c3d3316f",
)

traced_repo = trace(REPO)