

class CoqInterface:

    def __init__(self, kernel):
        self.kernel = kernel

    def __aenter__(self):
        """starts kernel"""
        await self.start()
        return self

    async def start(self):
        pass