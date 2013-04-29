cmpPrograms=../dist/build/cmpPrograms/cmpPrograms

(cd lib/.curry && ls *.fcy) | xargs -i -n 1 $cmpPrograms $1/.curry/'{}' "$1"2/.curry/'{}' | grep Not

exit 0
