
git config --global user.email "anon@example.com"
git config --global user.name "Anon"
git am "$(dirname "$0")"/*.patch