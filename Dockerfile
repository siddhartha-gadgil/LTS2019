FROM mmhelloworld/idris:1.3.1
WORKDIR /app
ADD . /app
CMD ["/app/test.sh"]
