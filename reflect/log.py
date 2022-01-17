from loguru import logger

def warn(s: str):
    logger.warning(s)

def error(s: str):
    logger.error(s)
